package me.fponzi.tlasmith.env;

import me.fponzi.tlasmith.ast.Operator;
import java.util.*;

public class Environment {
    private final Set<String> constants;
    private final Set<String> variables;
    private final Set<String> boundVariables;
    private final Set<String> operators;
    private final Map<String, Integer> operatorParameterCounts;
    private final Environment parent;

    public Environment() {
        this(null);
    }

    public Environment(Environment parent) {
        this.parent = parent;
        this.constants = new HashSet<>();
        this.variables = new HashSet<>();
        this.boundVariables = new HashSet<>();
        this.operators = new HashSet<>();
        this.operatorParameterCounts = new HashMap<>();
    }

    public void addConstant(String name) {
        Objects.requireNonNull(name, "Constant name cannot be null");
        constants.add(name);
    }

    public void addVariable(String name) {
        Objects.requireNonNull(name, "Variable name cannot be null");
        variables.add(name);
    }

    public void addBoundVariable(String name) {
        Objects.requireNonNull(name, "Bound variable name cannot be null");
        boundVariables.add(name);
    }

    public void addOperator(String name) {
        Objects.requireNonNull(name, "Operator name cannot be null");
        operators.add(name);
        operatorParameterCounts.put(name, 0); // Default to 0 parameters
    }

    public void addOperator(Operator operator) {
        Objects.requireNonNull(operator, "Operator cannot be null");
        String name = operator.getName();
        operators.add(name);
        operatorParameterCounts.put(name, operator.getParameters().size());
    }

    public void addConstants(Collection<String> constantNames) {
        constantNames.forEach(this::addConstant);
    }

    public void addVariables(Collection<String> variableNames) {
        variableNames.forEach(this::addVariable);
    }

    public void addOperators(Collection<String> operatorNames) {
        operatorNames.forEach(this::addOperator);
    }

    public boolean hasConstant(String name) {
        return constants.contains(name) || (parent != null && parent.hasConstant(name));
    }

    public boolean hasVariable(String name) {
        return variables.contains(name) || (parent != null && parent.hasVariable(name));
    }

    public boolean hasBoundVariable(String name) {
        return boundVariables.contains(name) || (parent != null && parent.hasBoundVariable(name));
    }

    public boolean hasOperator(String name) {
        return operators.contains(name) || (parent != null && parent.hasOperator(name));
    }

    public boolean hasIdentifier(String name) {
        return hasConstant(name) || hasVariable(name) || hasBoundVariable(name) || hasOperator(name);
    }

    public Set<String> getAllConstants() {
        Set<String> result = new HashSet<>(constants);
        if (parent != null) {
            result.addAll(parent.getAllConstants());
        }
        return result;
    }

    public Set<String> getAllVariables() {
        Set<String> result = new HashSet<>(variables);
        if (parent != null) {
            result.addAll(parent.getAllVariables());
        }
        return result;
    }

    public Set<String> getAllBoundVariables() {
        Set<String> result = new HashSet<>(boundVariables);
        if (parent != null) {
            result.addAll(parent.getAllBoundVariables());
        }
        return result;
    }

    public Set<String> getAllOperators() {
        Set<String> result = new HashSet<>(operators);
        if (parent != null) {
            result.addAll(parent.getAllOperators());
        }
        return result;
    }

    public Set<String> getAllIdentifiers() {
        Set<String> result = new HashSet<>();
        result.addAll(getAllConstants());
        result.addAll(getAllVariables());
        result.addAll(getAllBoundVariables());
        result.addAll(getAllOperators());
        return result;
    }

    public List<String> getAvailableConstants() {
        return new ArrayList<>(getAllConstants());
    }

    public List<String> getAvailableVariables() {
        return new ArrayList<>(getAllVariables());
    }

    public List<String> getAvailableOperators() {
        return new ArrayList<>(getAllOperators());
    }

    public List<String> getZeroParameterOperators() {
        List<String> result = new ArrayList<>();

        // Add local zero-parameter operators
        for (String opName : operators) {
            if (operatorParameterCounts.getOrDefault(opName, 0) == 0) {
                result.add(opName);
            }
        }

        // Add parent's zero-parameter operators
        if (parent != null) {
            result.addAll(parent.getZeroParameterOperators());
        }

        return result;
    }

    public List<String> getAvailableIdentifiers() {
        return new ArrayList<>(getAllIdentifiers());
    }

    public Environment createChild() {
        return new Environment(this);
    }

    public Environment createChildWithParameters(Collection<String> parameterNames) {
        Environment child = createChild();
        child.addBoundVariables(parameterNames);
        return child;
    }

    public void addBoundVariables(Collection<String> boundVariableNames) {
        boundVariableNames.forEach(this::addBoundVariable);
    }

    public boolean isEmpty() {
        return constants.isEmpty() && variables.isEmpty() && boundVariables.isEmpty() && operators.isEmpty() &&
               (parent == null || parent.isEmpty());
    }

    public int getTotalIdentifierCount() {
        return getAllIdentifiers().size();
    }

    @Override
    public String toString() {
        return "Environment{" +
               "constants=" + constants +
               ", variables=" + variables +
               ", boundVars=" + boundVariables +
               ", operators=" + operators +
               ", hasParent=" + (parent != null) +
               "}";
    }
}