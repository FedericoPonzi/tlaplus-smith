package me.fponzi.tlasmith.ast;

import java.util.Objects;

public class Formula implements Expr {
    private final String name;
    private final Expr expression;
    private final FormulaType type;

    public enum FormulaType {
        INIT,    // Initial state predicate
        NEXT,    // Next-state relation
        INVARIANT, // State invariant
        PROPERTY   // General property
    }

    public Formula(String name, Expr expression, FormulaType type) {
        this.name = Objects.requireNonNull(name, "Formula name cannot be null");
        this.expression = Objects.requireNonNull(expression, "Expression cannot be null");
        this.type = Objects.requireNonNull(type, "Formula type cannot be null");
    }

    public String getName() {
        return name;
    }

    public Expr getExpression() {
        return expression;
    }

    public FormulaType getType() {
        return type;
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
        Formula formula = (Formula) obj;
        return Objects.equals(name, formula.name) &&
               Objects.equals(expression, formula.expression) &&
               type == formula.type;
    }

    @Override
    public int hashCode() {
        return Objects.hash(name, expression, type);
    }

    @Override
    public String toString() {
        return "Formula{" + name + ", " + type + "}";
    }
}