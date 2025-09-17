package me.fponzi.tlasmith.ast;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class ExprTest {

    @Test
    void testVarCreation() {
        Var var = new Var("x");
        assertEquals("x", var.getName());
        assertEquals("x", var.toTLAString());
    }

    @Test
    void testVarEquality() {
        Var var1 = new Var("x");
        Var var2 = new Var("x");
        Var var3 = new Var("y");

        assertEquals(var1, var2);
        assertNotEquals(var1, var3);
        assertEquals(var1.hashCode(), var2.hashCode());
    }

    @Test
    void testVarNullName() {
        assertThrows(NullPointerException.class, () -> new Var(null));
    }

    @Test
    void testConstCreation() {
        Const constant = new Const("N");
        assertEquals("N", constant.getName());
        assertEquals("N", constant.toTLAString());
    }

    @Test
    void testConstEquality() {
        Const const1 = new Const("N");
        Const const2 = new Const("N");
        Const const3 = new Const("M");

        assertEquals(const1, const2);
        assertNotEquals(const1, const3);
        assertEquals(const1.hashCode(), const2.hashCode());
    }

    @Test
    void testOperatorCreation() {
        Var x = new Var("x");
        Operator op = new Operator("Op", x);

        assertEquals("Op", op.getName());
        assertEquals(x, op.getExpression());
        assertEquals("Op == x", op.toDefinitionString());
    }

    @Test
    void testOperatorEquality() {
        Var x = new Var("x");
        Var y = new Var("y");

        Operator op1 = new Operator("Op", x);
        Operator op2 = new Operator("Op", x);
        Operator op3 = new Operator("Op", y);
        Operator op4 = new Operator("Op2", x);

        assertEquals(op1, op2);
        assertNotEquals(op1, op3);
        assertNotEquals(op1, op4);
        assertEquals(op1.hashCode(), op2.hashCode());
    }

    @Test
    void testOperatorNullValues() {
        Var x = new Var("x");
        assertThrows(NullPointerException.class, () -> new Operator(null, x));
        assertThrows(NullPointerException.class, () -> new Operator("Op", null));
    }

    @Test
    void testOperatorWithComplexExpression() {
        Var x = new Var("x");
        Literal one = new Literal(1);
        BinaryOp expr = new BinaryOp(BinaryOp.Operator.PLUS, x, one);

        Operator op = new Operator("IncrementX", expr);

        assertEquals("IncrementX", op.getName());
        assertEquals(expr, op.getExpression());
        assertEquals("IncrementX == x + 1", op.toDefinitionString());
    }

    @Test
    void testLiteralBoolean() {
        Literal trueL = Literal.trueLiteral();
        Literal falseL = Literal.falseLiteral();

        assertEquals(Literal.LiteralType.BOOLEAN, trueL.getType());
        assertEquals(true, trueL.getValue());
        assertEquals("TRUE", trueL.toTLAString());

        assertEquals(Literal.LiteralType.BOOLEAN, falseL.getType());
        assertEquals(false, falseL.getValue());
        assertEquals("FALSE", falseL.toTLAString());
    }

    @Test
    void testLiteralInteger() {
        Literal intLit = new Literal(42);
        assertEquals(Literal.LiteralType.INTEGER, intLit.getType());
        assertEquals(42, intLit.getValue());
        assertEquals("42", intLit.toTLAString());
    }

    @Test
    void testLiteralString() {
        Literal strLit = new Literal("hello");
        assertEquals(Literal.LiteralType.STRING, strLit.getType());
        assertEquals("hello", strLit.getValue());
        assertEquals("\"hello\"", strLit.toTLAString());
    }

    @Test
    void testBinaryOpCreation() {
        Var x = new Var("x");
        Literal five = new Literal(5);
        BinaryOp plusOp = new BinaryOp(BinaryOp.Operator.PLUS, x, five);

        assertEquals(BinaryOp.Operator.PLUS, plusOp.getOperator());
        assertEquals(x, plusOp.getLeft());
        assertEquals(five, plusOp.getRight());
        assertEquals("x + 5", plusOp.toTLAString());
    }

    @Test
    void testBinaryOpLogical() {
        Literal trueL = Literal.trueLiteral();
        Literal falseL = Literal.falseLiteral();
        BinaryOp andOp = new BinaryOp(BinaryOp.Operator.AND, trueL, falseL);

        assertEquals(BinaryOp.Operator.AND, andOp.getOperator());
        assertEquals("(TRUE /\\ FALSE)", andOp.toTLAString());
    }

    @Test
    void testBinaryOpNullArguments() {
        Var x = new Var("x");
        Literal five = new Literal(5);

        assertThrows(NullPointerException.class,
            () -> new BinaryOp(null, x, five));
        assertThrows(NullPointerException.class,
            () -> new BinaryOp(BinaryOp.Operator.PLUS, null, five));
        assertThrows(NullPointerException.class,
            () -> new BinaryOp(BinaryOp.Operator.PLUS, x, null));
    }

    @Test
    void testOperatorProperties() {
        assertTrue(BinaryOp.Operator.PLUS.isArithmetic());
        assertFalse(BinaryOp.Operator.PLUS.isLogical());

        assertTrue(BinaryOp.Operator.AND.isLogical());
        assertFalse(BinaryOp.Operator.AND.isArithmetic());

        assertTrue(BinaryOp.Operator.EQUALS.isComparison());
        assertFalse(BinaryOp.Operator.EQUALS.isLogical());

        assertTrue(BinaryOp.Operator.IN.isSetRelation());
        assertFalse(BinaryOp.Operator.IN.isArithmetic());
    }

    @Test
    void testFormulaCreation() {
        Var x = new Var("x");
        Literal zero = new Literal(0);
        BinaryOp expr = new BinaryOp(BinaryOp.Operator.EQUALS, x, zero);

        Formula formula = new Formula("Init", expr, Formula.FormulaType.INIT);

        assertEquals("Init", formula.getName());
        assertEquals(expr, formula.getExpression());
        assertEquals(Formula.FormulaType.INIT, formula.getType());
        assertEquals("Init == x = 0", formula.toDefinitionString());
    }

    @Test
    void testNestedBinaryOps() {
        Var x = new Var("x");
        Var y = new Var("y");
        Literal one = new Literal(1);

        BinaryOp xPlusOne = new BinaryOp(BinaryOp.Operator.PLUS, x, one);
        BinaryOp yEqualsXPlusOne = new BinaryOp(BinaryOp.Operator.EQUALS, y, xPlusOne);

        assertEquals("y = x + 1", yEqualsXPlusOne.toTLAString());
    }
}