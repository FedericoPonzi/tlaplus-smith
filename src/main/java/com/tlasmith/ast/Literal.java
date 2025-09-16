package com.tlasmith.ast;

import java.util.Objects;

public class Literal implements Expr {
    private final Object value;
    private final LiteralType type;

    public enum LiteralType {
        BOOLEAN,
        INTEGER,
        STRING
    }

    public Literal(boolean value) {
        this.value = value;
        this.type = LiteralType.BOOLEAN;
    }

    public Literal(int value) {
        this.value = value;
        this.type = LiteralType.INTEGER;
    }

    public Literal(String value) {
        this.value = Objects.requireNonNull(value, "String literal cannot be null");
        this.type = LiteralType.STRING;
    }

    public Object getValue() {
        return value;
    }

    public LiteralType getType() {
        return type;
    }

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        Literal literal = (Literal) obj;
        return Objects.equals(value, literal.value) && type == literal.type;
    }

    @Override
    public int hashCode() {
        return Objects.hash(value, type);
    }

    @Override
    public String toString() {
        if (type == LiteralType.STRING) {
            return "\"" + value + "\"";
        } else if (type == LiteralType.BOOLEAN) {
            return (Boolean) value ? "TRUE" : "FALSE";
        }
        return value.toString();
    }

    public static Literal trueLiteral() {
        return new Literal(true);
    }

    public static Literal falseLiteral() {
        return new Literal(false);
    }
}