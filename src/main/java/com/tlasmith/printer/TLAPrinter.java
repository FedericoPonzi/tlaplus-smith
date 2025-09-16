package com.tlasmith.printer;

import com.tlasmith.ast.*;

public class TLAPrinter implements ExprVisitor<String> {
    private int indentLevel = 0;
    private static final String INDENT = "  ";

    public static String print(Expr expr) {
        return new TLAPrinter().visit(expr);
    }

    public static String print(Formula formula) {
        return new TLAPrinter().printFormula(formula);
    }

    public static String print(Spec spec) {
        return new TLAPrinter().printSpec(spec);
    }

    public String visit(Expr expr) {
        return expr.accept(this);
    }

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

        // Determine if parentheses are needed based on operator precedence and type
        boolean needsParens = needsParentheses(binaryOp);

        if (needsParens) {
            return "(" + left + " " + op + " " + right + ")";
        } else {
            return left + " " + op + " " + right;
        }
    }

    @Override
    public String visit(Formula formula) {
        return formula.getExpression().accept(this);
    }

    private boolean needsParentheses(BinaryOp binaryOp) {
        // ALWAYS use parentheses to completely eliminate precedence conflicts
        // TLA+ has complex precedence rules, so we err on the side of safety
        return true;
    }

    public String printFormula(Formula formula) {
        StringBuilder sb = new StringBuilder();

        sb.append(formula.getName()).append(" == ");

        String exprStr = formula.getExpression().accept(this);

        // For multi-line expressions, add proper formatting
        if (exprStr.length() > 60 || exprStr.contains("(/\\") || exprStr.contains("(\\/")) {
            sb.append("\n").append(addIndent(exprStr, 1));
        } else {
            sb.append(exprStr);
        }

        return sb.toString();
    }

    public String printSpec(Spec spec) {
        StringBuilder sb = new StringBuilder();

        // Module header
        String header = "---- MODULE " + spec.getModuleName() + " ----";
        sb.append(header).append("\n");

        // EXTENDS
        if (!spec.getExtendsModules().isEmpty()) {
            sb.append("EXTENDS ").append(String.join(", ", spec.getExtendsModules())).append("\n");
        }

        // CONSTANTS
        if (!spec.getConstants().isEmpty()) {
            sb.append("CONSTANTS ").append(String.join(", ", spec.getConstants())).append("\n");
        }

        // VARIABLES
        if (!spec.getVariables().isEmpty()) {
            sb.append("VARIABLES ").append(String.join(", ", spec.getVariables())).append("\n");
        }

        sb.append("\n");

        // Formula definitions
        for (Formula formula : spec.getFormulas()) {
            sb.append(printFormula(formula)).append("\n\n");
        }

        // Specification formula (if Init and Next exist)
        if (spec.getInit().isPresent() && spec.getNext().isPresent()) {
            String varsStr = spec.getVariables().isEmpty() ?
                "" : "<<" + String.join(", ", spec.getVariables()) + ">>";

            sb.append("Spec == ").append(spec.getInit().get().getName())
              .append(" /\\ [][").append(spec.getNext().get().getName())
              .append("]_").append(varsStr).append("\n\n");
        }

        // Module footer
        sb.append("====");

        return sb.toString();
    }

    private String addIndent(String text, int levels) {
        String indentStr = INDENT.repeat(levels);
        return text.lines()
                .map(line -> line.trim().isEmpty() ? line : indentStr + line)
                .reduce((a, b) -> a + "\n" + b)
                .orElse(text);
    }

    public void increaseIndent() {
        indentLevel++;
    }

    public void decreaseIndent() {
        indentLevel = Math.max(0, indentLevel - 1);
    }

    private String getCurrentIndent() {
        return INDENT.repeat(indentLevel);
    }
}