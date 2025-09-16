package com.tlasmith.ast;

import java.util.Objects;

public class Var implements Expr {
    private final String name;

    public Var(String name) {
        this.name = Objects.requireNonNull(name, "Variable name cannot be null");
    }

    public String getName() {
        return name;
    }

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        Var var = (Var) obj;
        return Objects.equals(name, var.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    @Override
    public String toString() {
        return "Var{" + name + "}";
    }
}