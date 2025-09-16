package me.fponzi.tlasmith.ast;

import java.util.Objects;

public class BinaryOp implements Expr {
    private final Operator operator;
    private final Expr left;
    private final Expr right;

    public enum Operator {
        PLUS("+", false),
        MINUS("-", false),
        MULTIPLY("*", false),
        AND("/\\", true),
        OR("\\/", true),
        IMPLIES("=>", true),
        EQUALS("=", false),
        NOT_EQUALS("#", false),
        IN("\\in", false),
        SUBSETEQ("\\subseteq", false),
        SUBSET("\\subset", false),
        LESS_THAN("<", false),
        GREATER_THAN(">", false),
        LESS_EQUAL("<=", false),
        GREATER_EQUAL(">=", false);

        private final String symbol;
        private final boolean needsParentheses;

        Operator(String symbol, boolean needsParentheses) {
            this.symbol = symbol;
            this.needsParentheses = needsParentheses;
        }

        public String getSymbol() {
            return symbol;
        }

        public boolean needsParentheses() {
            return needsParentheses;
        }

        public boolean isArithmetic() {
            return this == PLUS || this == MINUS || this == MULTIPLY;
        }

        public boolean isLogical() {
            return this == AND || this == OR || this == IMPLIES;
        }

        public boolean isComparison() {
            return this == EQUALS || this == NOT_EQUALS || this == LESS_THAN ||
                   this == GREATER_THAN || this == LESS_EQUAL || this == GREATER_EQUAL;
        }

        public boolean isSetRelation() {
            return this == IN || this == SUBSETEQ || this == SUBSET;
        }
    }

    public BinaryOp(Operator operator, Expr left, Expr right) {
        this.operator = Objects.requireNonNull(operator, "Operator cannot be null");
        this.left = Objects.requireNonNull(left, "Left expression cannot be null");
        this.right = Objects.requireNonNull(right, "Right expression cannot be null");
    }

    public Operator getOperator() {
        return operator;
    }

    public Expr getLeft() {
        return left;
    }

    public Expr getRight() {
        return right;
    }

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        BinaryOp binaryOp = (BinaryOp) obj;
        return operator == binaryOp.operator &&
               Objects.equals(left, binaryOp.left) &&
               Objects.equals(right, binaryOp.right);
    }

    @Override
    public int hashCode() {
        return Objects.hash(operator, left, right);
    }

    @Override
    public String toString() {
        return "BinaryOp{" + operator + ", " + left + ", " + right + "}";
    }
}