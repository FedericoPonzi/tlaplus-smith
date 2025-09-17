package me.fponzi.tlasmith.ast;

public interface ExprVisitor<T> {
    T visit(Var var);
    T visit(Const constant);
    T visit(Literal literal);
    T visit(BinaryOp binaryOp);
    T visit(Formula formula);
    T visit(Operator operator);
}