package me.fponzi.tlasmith.ast;

import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * Represents an operator declaration in TLA+, in the form "Op == expr" or "Op(a,b) == expr".
 * This is different from Formula which is used for special formulas like Init/Next.
 */
public class Operator implements Expr {
    private final String name;
    private final List<String> parameters;
    private final Expr expression;

    public Operator(String name, Expr expression) {
        this(name, Collections.emptyList(), expression);
    }

    public Operator(String name, List<String> parameters, Expr expression) {
        this.name = Objects.requireNonNull(name, "Operator name cannot be null");
        this.parameters = List.copyOf(Objects.requireNonNull(parameters, "Parameters cannot be null"));
        this.expression = Objects.requireNonNull(expression, "Expression cannot be null");
    }

    public String getName() {
        return name;
    }

    public List<String> getParameters() {
        return parameters;
    }

    public Expr getExpression() {
        return expression;
    }

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public String toDefinitionString() {
        if (parameters.isEmpty()) {
            return name + " == " + expression.toTLAString();
        } else {
            return name + "(" + String.join(", ", parameters) + ") == " + expression.toTLAString();
        }
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        Operator operator = (Operator) obj;
        return Objects.equals(name, operator.name) &&
               Objects.equals(parameters, operator.parameters) &&
               Objects.equals(expression, operator.expression);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name, parameters, expression);
    }

    @Override
    public String toString() {
        return "Operator{" + name + "}";
    }
}