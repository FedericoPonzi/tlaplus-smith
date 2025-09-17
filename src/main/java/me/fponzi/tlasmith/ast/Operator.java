package me.fponzi.tlasmith.ast;

import java.util.Objects;

/**
 * Represents an operator declaration in TLA+, in the form "Op == expr".
 * This is different from Formula which is used for special formulas like Init/Next.
 */
public class Operator implements Expr {
    private final String name;
    private final Expr expression;

    public Operator(String name, Expr expression) {
        this.name = Objects.requireNonNull(name, "Operator name cannot be null");
        this.expression = Objects.requireNonNull(expression, "Expression cannot be null");
    }

    public String getName() {
        return name;
    }

    public Expr getExpression() {
        return expression;
    }

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public String toDefinitionString() {
        return name + " == " + expression.toTLAString();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        Operator operator = (Operator) obj;
        return Objects.equals(name, operator.name) &&
               Objects.equals(expression, operator.expression);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name, expression);
    }

    @Override
    public String toString() {
        return "Operator{" + name + "}";
    }
}