import java.math.BigInteger;

public class ExprFactor extends Factor {
    private Expression expr;

    public ExprFactor(String string) {
        //ExprCheck.checkExprFactor(string);
        String str = getFormattedExpr(string);
        expr = new Expression(str);
    }

    public ExprFactor(String string, String exprFactor) {
        if (string.equals("(E)")) {
            this.expr = new Expression(exprFactor);
        } else {
            System.out.println("Wrong ExprFactor!"
                    + "\tstring:" + string + "\texprFactor" + exprFactor);
        }
    }

    private String getFormattedExpr(String string) {
        String str = new String();
        if (string.charAt(0) == '('
                && string.charAt(string.length() - 1) == ')') {
            // 防止 (x) + (x) -> x)+(x
            // e.g. (x) + (x) -> [x)+(x] , 括号不匹配，不能去掉"最外层"括号
            str = "[" + string.substring(1, string.length() - 1) + "]";
            if (BracketsHandler.isMatch(str)) {
                str = string.substring(1, string.length() - 1);
            } else {
                str = string;
            }

        } else {
            str = string;
        }
        return str;
    }

    @Override
    public BigInteger getIndex() {
        return BigInteger.ONE;
    }

    @Override
    public Term diff() {
        Term newTerm = new Term();
        String temp = this.expr.diff().toString();
        ExprFactor newExprFactor = new ExprFactor(temp);

        newTerm.addFactor(newExprFactor);

        return newTerm;
    }

    @Override
    public String toString() {
        String str = "(" + expr.toString() + ")";

        return str;
    }
}
