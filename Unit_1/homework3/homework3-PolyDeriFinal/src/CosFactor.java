import java.math.BigInteger;

public class CosFactor extends Factor {
    private BigInteger index;
    private Factor factor;

    public CosFactor(BigInteger index, Factor factor) {
        this.index = index;
        this.factor = factor;

        if (this.index.compareTo(ExprCheck.tenThousand) > 0) {
            ExprCheck.formatError();
        }
    }

    public CosFactor(String string, String exprFactor) {
        ExprCheck.checkCosFactor(string);
        ExprCheck.checkFactor(exprFactor);  // 检查是否是因子

        if (string.contains("^")) {
            String str = string.substring(string.indexOf('^') + 1);
            this.index = new BigInteger(str);
        } else {
            this.index = BigInteger.ONE;
        }

        this.factor = new ExprFactor(exprFactor);

        if (this.index.compareTo(ExprCheck.tenThousand) > 0) {
            ExprCheck.formatError();
        }
    }

    public BigInteger getIndex() {
        return index;
    }

    @Override
    public Term diff() {
        Term newTerm = new Term();
        BigInteger newIndex = this.index.subtract(BigInteger.ONE);

        if (this.index.equals(BigInteger.ZERO)) {
            return null;
        }

        ConstFactor newCoef = new ConstFactor(
                this.index.multiply(BigInteger.valueOf(-1)));   // -c
        // sin(factor)
        SinFactor newSinFactor = new SinFactor(BigInteger.ONE, factor);
        // cos(factor)^c-1
        CosFactor newCosFactor = new CosFactor(newIndex, factor);
        Term diffedFactor = factor.diff();                        // factor'
        ExprFactor newExprFactor = new ExprFactor(diffedFactor.toString());

        //newTerm.add(newCoef, newSinFactor, newCosFactor, newExprFactor);
        newTerm.addFactor(newCoef);
        newTerm.addFactor(newSinFactor);
        newTerm.addFactor(newCosFactor);
        newTerm.addFactor(newExprFactor);

        return newTerm;
    }

    @Override
    public String toString() {
        String res;

        if (this.index.equals(BigInteger.ZERO)) {
            res = "1";
        } else if (this.index.equals(BigInteger.ONE)) {
            res = "cos(" + factor.toString() + ")";
        } else {
            res = "cos(" + factor.toString() + ")^" + index.toString();
        }

        return res;
    }
}
