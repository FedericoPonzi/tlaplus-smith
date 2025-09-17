package me.fponzi.tlasmith.generator;

import me.fponzi.tlasmith.ast.*;
import me.fponzi.tlasmith.env.Environment;
import me.fponzi.tlasmith.validation.SanyValidator;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import static org.junit.jupiter.api.Assertions.*;

import java.util.Arrays;

class GeneratorTest {
    private Generator generator;
    private Environment environment;
    private SanyValidator validator;

    @BeforeEach
    void setUp() {
        generator = new Generator(12345); // Use fixed seed for deterministic tests
        environment = new Environment();
        environment.addVariables(Arrays.asList("x", "y", "state"));
        environment.addConstants(Arrays.asList("N", "MaxVal"));
        validator = new SanyValidator();
    }

    @Test
    void testGenerateSpec() {
        Spec spec = generator.generateSpec("TestModule");

        assertNotNull(spec);
        assertEquals("TestModule", spec.getModuleName());
        assertFalse(spec.getVariables().isEmpty());
        assertFalse(spec.getConstants().isEmpty());
        assertTrue(spec.getExtendsModules().contains("Integers"));

        // Should have Init and Next formulas
        assertTrue(spec.getInit().isPresent());
        assertTrue(spec.getNext().isPresent());

        assertEquals(Formula.FormulaType.INIT, spec.getInit().get().getType());
        assertEquals(Formula.FormulaType.NEXT, spec.getNext().get().getType());

        // Generated spec must be SANY-valid
        SanyValidator.ValidationResult result = validator.validateTLAText(spec.toTLAString());
        assertTrue(result.isValid(), "Generated spec must be SANY-valid. Errors: " + result.getErrors());
    }

    @Test
    void testGenerateSpecReproducible() {
        Generator gen1 = new Generator(42);
        Generator gen2 = new Generator(42);

        Spec spec1 = gen1.generateSpec("Test");
        Spec spec2 = gen2.generateSpec("Test");

        // With same seed, should generate identical specs
        assertEquals(spec1.getVariables(), spec2.getVariables());
        assertEquals(spec1.getConstants(), spec2.getConstants());
        // Note: Expressions might be complex to compare, but basic structure should match
    }

    @Test
    void testGenerateExpression() {
        Expr expr = generator.generateExpression(environment, 2, false);
        assertNotNull(expr);

        // Should be a valid expression that can be converted to TLA+ string
        String tlaString = expr.toTLAString();
        assertNotNull(tlaString);
        assertFalse(tlaString.trim().isEmpty());
    }

    @Test
    void testGenerateBooleanExpression() {
        Expr expr = generator.generateExpression(environment, 3, true);
        assertNotNull(expr);

        // Verify it generates valid TLA+ text
        String tlaString = expr.toTLAString();
        assertNotNull(tlaString);
        assertFalse(tlaString.trim().isEmpty());

        // Boolean expressions should generate valid TLA+ output
        // The specific content depends on random generation, so we just verify it's reasonable
        assertTrue(tlaString.matches(".*[A-Za-z0-9+\\-=<>\"\\(\\)\\/\\\\\\s]+.*"),
                  "Generated expression should contain valid TLA+ characters: " + tlaString);
    }

    @Test
    void testGenerateWithEmptyEnvironment() {
        Environment emptyEnv = new Environment();
        Expr expr = generator.generateExpression(emptyEnv, 2, false);

        // Should still generate something (likely literals only)
        assertNotNull(expr);
        assertTrue(expr instanceof Literal);
    }

    @Test
    void testGenerateWithZeroDepth() {
        Expr expr = generator.generateExpression(environment, 0, false);

        // Should generate atomic expression (literal, var, or const)
        assertNotNull(expr);
        assertTrue(expr instanceof Literal || expr instanceof Var || expr instanceof Const);
    }

    @Test
    void testGenerateFormula() {
        Formula formula = generator.generateFormula("TestFormula", environment, Formula.FormulaType.INVARIANT);

        assertNotNull(formula);
        assertEquals("TestFormula", formula.getName());
        assertEquals(Formula.FormulaType.INVARIANT, formula.getType());
        assertNotNull(formula.getExpression());

        // Should generate valid definition string
        String defString = formula.toDefinitionString();
        assertTrue(defString.startsWith("TestFormula == "));
    }

    @Test
    void testDefaultConfig() {
        Generator.GeneratorConfig config = Generator.GeneratorConfig.defaultConfig();

        assertNotNull(config);
        assertTrue(config.maxDepth > 0);
        assertTrue(config.minVariables >= 0);
        assertTrue(config.maxVariables >= config.minVariables);
        assertTrue(config.minConstants >= 0);
        assertTrue(config.maxConstants >= config.minConstants);

        // Probabilities should sum to reasonable values
        assertTrue(config.literalProbability >= 0 && config.literalProbability <= 1);
        assertTrue(config.variableProbability >= 0 && config.variableProbability <= 1);
        assertTrue(config.constantProbability >= 0 && config.constantProbability <= 1);
        assertTrue(config.binaryOpProbability >= 0 && config.binaryOpProbability <= 1);
    }

    @Test
    void testGeneratedSpecHasValidStructure() {
        Spec spec = generator.generateSpec("ValidTest");

        // Basic structure validation
        assertNotNull(spec.getModuleName());
        assertFalse(spec.getModuleName().isEmpty());

        // Should have at least some variables or constants
        assertTrue(!spec.getVariables().isEmpty() || !spec.getConstants().isEmpty());

        // If it has variables, should have appropriate formulas
        if (!spec.getVariables().isEmpty()) {
            assertTrue(spec.getInit().isPresent() || spec.getNext().isPresent());
        }

        // Should generate valid TLA+ text
        String tlaText = spec.toTLAString();
        assertNotNull(tlaText);
        assertFalse(tlaText.trim().isEmpty());
        assertTrue(tlaText.contains("---- MODULE"));
        assertTrue(tlaText.contains("===="));
    }

    @Test
    void testInitFormulaInitializesAllVariables() {
        Spec spec = generator.generateSpec("InitTest");

        // Spec should have an Init formula
        assertTrue(spec.getInit().isPresent());
        Formula initFormula = spec.getInit().get();

        // Get the TLA+ string representation of the Init formula
        String initString = initFormula.toDefinitionString();
        assertTrue(initString.startsWith("Init == "));

        // Each variable should be initialized (appear in the Init formula)
        for (String variable : spec.getVariables()) {
            assertTrue(initString.contains(variable + " ="),
                      "Variable '" + variable + "' should be initialized in Init formula: " + initString);
        }

        // Init should contain AND operators if multiple variables (except for single variable case)
        if (spec.getVariables().size() > 1) {
            assertTrue(initString.contains("/\\"),
                      "Multiple variables should be combined with AND (/\\) in Init: " + initString);
        }

        // Should be SANY-valid
        SanyValidator.ValidationResult result = validator.validateTLAText(spec.toTLAString());
        assertTrue(result.isValid(), "Spec with variable initialization must be SANY-valid. Errors: " + result.getErrors());
    }

    @Test
    void testInitFormulaWithSingleVariable() {
        // Create generator with config that ensures single variable
        Generator.GeneratorConfig singleVarConfig = new Generator.GeneratorConfig(
            3, 1, 1, // single variable
            0, 1, // optional constant
            0.5, 0.3, 0.1, 0.1
        );
        Generator singleVarGenerator = new Generator(new java.util.Random(54321), singleVarConfig);

        Spec spec = singleVarGenerator.generateSpec("SingleVarTest");

        // Should have exactly one variable
        assertEquals(1, spec.getVariables().size());

        // Init should initialize that variable
        assertTrue(spec.getInit().isPresent());
        String initString = spec.getInit().get().toDefinitionString();

        String variable = spec.getVariables().get(0);
        assertTrue(initString.contains(variable + " ="),
                  "Single variable '" + variable + "' should be initialized: " + initString);
    }

    @Test
    void testOperatorGeneration() {
        Spec spec = generator.generateSpec("OperatorTest");

        // Should potentially have operators (not guaranteed due to randomness)
        assertNotNull(spec.getOperators());

        // If operators exist, they should be valid
        for (Operator operator : spec.getOperators()) {
            assertNotNull(operator.getName());
            assertFalse(operator.getName().isEmpty());
            assertNotNull(operator.getExpression());

            // Operator should have valid definition string
            String defString = operator.toDefinitionString();
            assertTrue(defString.contains(" == "));
            assertTrue(defString.startsWith(operator.getName()));
        }

        // Spec should still be SANY-valid with operators
        SanyValidator.ValidationResult result = validator.validateTLAText(spec.toTLAString());
        assertTrue(result.isValid(), "Spec with operators must be SANY-valid. Errors: " + result.getErrors());
    }

    @Test
    void testSpecBuilderWithOperators() {
        Var x = new Var("x");
        Operator op1 = new Operator("Op1", x);
        Operator op2 = new Operator("Op2", new Literal(42));

        Spec spec = new Spec.Builder()
                .moduleName("TestModule")
                .extend("Integers")
                .variable("x")
                .operator(op1)
                .operator(op2)
                .build();

        assertEquals(2, spec.getOperators().size());
        assertTrue(spec.getOperators().contains(op1));
        assertTrue(spec.getOperators().contains(op2));

        // Should include operators in TLA+ output
        String tlaString = spec.toTLAString();
        assertTrue(tlaString.contains("Op1 == x"));
        assertTrue(tlaString.contains("Op2 == 42"));
    }

    @Test
    void testMultipleGenerations() {
        // Generate multiple specs to ensure no exceptions and all are valid
        for (int i = 0; i < 10; i++) {
            Spec spec = generator.generateSpec("Test" + i);
            assertNotNull(spec);
            assertNotNull(spec.toTLAString());

            // Each generated spec must be SANY-valid
            SanyValidator.ValidationResult result = validator.validateTLAText(spec.toTLAString());
            assertTrue(result.isValid(), "Generated spec Test" + i + " must be SANY-valid. Errors: " + result.getErrors());
        }
    }
}