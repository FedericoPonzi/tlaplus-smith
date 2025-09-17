package me.fponzi.tlasmith.generator;

import me.fponzi.tlasmith.ast.*;
import me.fponzi.tlasmith.env.Environment;

import java.util.*;
import java.util.stream.Collectors;

public class Generator {
    private final Random random;
    private final GeneratorConfig config;

    public static class GeneratorConfig {
        public final int maxDepth;
        public final int minVariables;
        public final int maxVariables;
        public final int minConstants;
        public final int maxConstants;
        public final double literalProbability;
        public final double variableProbability;
        public final double constantProbability;
        public final double binaryOpProbability;

        public GeneratorConfig(int maxDepth, int minVariables, int maxVariables,
                             int minConstants, int maxConstants,
                             double literalProbability, double variableProbability,
                             double constantProbability, double binaryOpProbability) {
            this.maxDepth = maxDepth;
            this.minVariables = minVariables;
            this.maxVariables = maxVariables;
            this.minConstants = minConstants;
            this.maxConstants = maxConstants;
            this.literalProbability = literalProbability;
            this.variableProbability = variableProbability;
            this.constantProbability = constantProbability;
            this.binaryOpProbability = binaryOpProbability;
        }

        public static GeneratorConfig defaultConfig() {
            return new GeneratorConfig(
                4,    // maxDepth
                2, 5, // min/maxVariables
                1, 3, // min/maxConstants
                0.3,  // literalProbability
                0.4,  // variableProbability
                0.2,  // constantProbability
                0.1   // binaryOpProbability
            );
        }
    }

    public Generator(Random random, GeneratorConfig config) {
        this.random = Objects.requireNonNull(random);
        this.config = Objects.requireNonNull(config);
    }

    public Generator() {
        this(new Random(), GeneratorConfig.defaultConfig());
    }

    public Generator(long seed) {
        this(new Random(seed), GeneratorConfig.defaultConfig());
    }

    public Spec generateSpec(String moduleName) {
        Environment env = new Environment();

        // Generate constants
        List<String> constants = generateIdentifierList("C", config.minConstants, config.maxConstants);
        env.addConstants(constants);

        // Generate variables
        List<String> variables = generateIdentifierList("x", config.minVariables, config.maxVariables);
        env.addVariables(variables);

        // Generate Init formula
        Formula initFormula = new Formula("Init", generateInitFormula(variables),
                                        Formula.FormulaType.INIT);

        // Generate Next formula
        Formula nextFormula = new Formula("Next", generateNextStateFormula(env, variables),
                                        Formula.FormulaType.NEXT);

        List<Formula> formulas = Arrays.asList(initFormula, nextFormula);

        return new Spec.Builder()
                .moduleName(moduleName)
                .extend("Integers")
                .constants(constants)
                .variables(variables)
                .formula(initFormula)
                .formula(nextFormula)
                .build();
    }

    private List<String> generateIdentifierList(String prefix, int min, int max) {
        int count = min + random.nextInt(max - min + 1);
        List<String> identifiers = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            identifiers.add(prefix + (i == 0 ? "" : String.valueOf(i + 1)));
        }
        return identifiers;
    }

    public Expr generateExpression(Environment env, int maxDepth, boolean preferBoolean) {
        if (maxDepth <= 0 || env.isEmpty()) {
            return generateAtomicExpression(env, preferBoolean);
        }

        double choice = random.nextDouble();
        double cumulativeProb = 0.0;

        // Literal
        cumulativeProb += config.literalProbability;
        if (choice < cumulativeProb) {
            return generateLiteral(preferBoolean);
        }

        // Variable
        cumulativeProb += config.variableProbability;
        if (choice < cumulativeProb && !env.getAllVariables().isEmpty()) {
            return generateVariable(env);
        }

        // Constant
        cumulativeProb += config.constantProbability;
        if (choice < cumulativeProb && !env.getAllConstants().isEmpty()) {
            return generateConstant(env);
        }

        // Binary operation (default)
        return generateBinaryOperation(env, maxDepth - 1, preferBoolean);
    }

    private Expr generateAtomicExpression(Environment env, boolean preferBoolean) {
        List<Expr> candidates = new ArrayList<>();

        // Always include literals
        candidates.add(generateLiteral(preferBoolean));

        // Add variables if available
        if (!env.getAllVariables().isEmpty()) {
            candidates.add(generateVariable(env));
        }

        // Add constants if available
        if (!env.getAllConstants().isEmpty()) {
            candidates.add(generateConstant(env));
        }

        return candidates.get(random.nextInt(candidates.size()));
    }

    private Expr generateLiteral(boolean preferBoolean) {
        if (preferBoolean || random.nextBoolean()) {
            return random.nextBoolean() ? Literal.trueLiteral() : Literal.falseLiteral();
        } else {
            return new Literal(random.nextInt(10));
        }
    }

    private Expr generateVariable(Environment env) {
        List<String> vars = env.getAvailableVariables();
        String varName = vars.get(random.nextInt(vars.size()));
        return new Var(varName);
    }

    private Expr generateConstant(Environment env) {
        List<String> consts = env.getAvailableConstants();
        String constName = consts.get(random.nextInt(consts.size()));
        return new Const(constName);
    }

    private Expr generateBinaryOperation(Environment env, int maxDepth, boolean preferBoolean) {
        BinaryOp.Operator operator = chooseOperator(preferBoolean);

        boolean needsBooleanOperands = operator.isLogical();

        Expr left = generateExpression(env, maxDepth, needsBooleanOperands);
        Expr right = generateExpression(env, maxDepth, needsBooleanOperands);

        return new BinaryOp(operator, left, right);
    }

    private BinaryOp.Operator chooseOperator(boolean preferBoolean) {
        List<BinaryOp.Operator> operators = new ArrayList<>();

        if (preferBoolean) {
            operators.addAll(Arrays.asList(
                BinaryOp.Operator.AND,
                BinaryOp.Operator.OR,
                BinaryOp.Operator.IMPLIES
            ));
        }

        // Always include comparison and arithmetic operators
        operators.addAll(Arrays.asList(
            BinaryOp.Operator.EQUALS,
            BinaryOp.Operator.NOT_EQUALS,
            BinaryOp.Operator.LESS_THAN,
            BinaryOp.Operator.GREATER_THAN,
            BinaryOp.Operator.PLUS,
            BinaryOp.Operator.MINUS
        ));

        return operators.get(random.nextInt(operators.size()));
    }

    private Expr generateInitFormula(List<String> variables) {
        if (variables.isEmpty()) {
            return Literal.trueLiteral();
        }

        List<Expr> initializations = new ArrayList<>();

        // Initialize each variable to a specific value
        for (String var : variables) {
            Var variable = new Var(var);
            Expr initialValue = generateInitialValue();
            initializations.add(new BinaryOp(BinaryOp.Operator.EQUALS, variable, initialValue));
        }

        // Combine all initializations with AND
        Expr result = initializations.get(0);
        for (int i = 1; i < initializations.size(); i++) {
            result = new BinaryOp(BinaryOp.Operator.AND, result, initializations.get(i));
        }

        return result;
    }

    private Expr generateInitialValue() {
        // Generate a simple initial value (integer literal or boolean)
        if (random.nextBoolean()) {
            return new Literal(random.nextInt(5)); // 0-4 for variety
        } else {
            return random.nextBoolean() ? Literal.trueLiteral() : Literal.falseLiteral();
        }
    }

    private Expr generateNextStateFormula(Environment env, List<String> variables) {
        if (variables.isEmpty()) {
            return generateExpression(env, config.maxDepth, true);
        }

        // Create a disjunction of possible state transitions
        List<Expr> transitions = new ArrayList<>();

        for (int i = 0; i < Math.min(3, variables.size()); i++) {
            Expr condition = generateExpression(env, 2, true);
            Expr stateChange = generateStateChange(variables);

            if (transitions.isEmpty()) {
                transitions.add(new BinaryOp(BinaryOp.Operator.AND, condition, stateChange));
            } else {
                Expr combined = new BinaryOp(BinaryOp.Operator.AND, condition, stateChange);
                Expr last = transitions.remove(transitions.size() - 1);
                transitions.add(new BinaryOp(BinaryOp.Operator.OR, last, combined));
            }
        }

        return transitions.isEmpty() ? generateExpression(env, config.maxDepth, true) : transitions.get(0);
    }

    private Expr generateStateChange(List<String> variables) {
        List<Expr> changes = new ArrayList<>();

        // ALL variables must be assigned in TLA+ Next formulas
        for (String var : variables) {
            Var primed = new Var(var + "'");
            Expr value;

            if (random.nextBoolean()) {
                // Keep same value
                value = new Var(var);
            } else {
                // Change value
                value = new BinaryOp(BinaryOp.Operator.PLUS, new Var(var), new Literal(1));
            }

            changes.add(new BinaryOp(BinaryOp.Operator.EQUALS, primed, value));
        }

        if (changes.isEmpty()) {
            // Fallback for empty variables list
            return Literal.trueLiteral();
        }

        // Combine with AND
        Expr result = changes.get(0);
        for (int i = 1; i < changes.size(); i++) {
            result = new BinaryOp(BinaryOp.Operator.AND, result, changes.get(i));
        }

        return result;
    }

    public Formula generateFormula(String name, Environment env, Formula.FormulaType type) {
        boolean preferBoolean = (type != Formula.FormulaType.PROPERTY);
        Expr expr = generateExpression(env, config.maxDepth, preferBoolean);
        return new Formula(name, expr, type);
    }
}