package me.fponzi.tlasmith.ast;

public interface Expr {
    <T> T accept(ExprVisitor<T> visitor);

    default String toTLAString() {
        return accept(new TLAStringVisitor());
    }
}


class TLAStringVisitor implements ExprVisitor<String> {
    @Override
    public String visit(Var var) {
        return var.getName();
    }

    @Override
    public String visit(Const constant) {
        return constant.getName();
    }

    @Override
    public String visit(Literal literal) {
        switch (literal.getType()) {
            case BOOLEAN:
                return (Boolean) literal.getValue() ? "TRUE" : "FALSE";
            case INTEGER:
                return literal.getValue().toString();
            case STRING:
                return "\"" + literal.getValue() + "\"";
            default:
                return literal.getValue().toString();
        }
    }

    @Override
    public String visit(BinaryOp binaryOp) {
        String left = binaryOp.getLeft().accept(this);
        String right = binaryOp.getRight().accept(this);
        String op = binaryOp.getOperator().getSymbol();

        if (binaryOp.getOperator().needsParentheses()) {
            return "(" + left + " " + op + " " + right + ")";
        }
        return left + " " + op + " " + right;
    }

    @Override
    public String visit(Formula formula) {
        return formula.getExpression().accept(this);
    }
}