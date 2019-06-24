import java.math.BigInteger;

public class SinFactor extends Factor {
    private BigInteger index;
    private Factor factor;

    public SinFactor(BigInteger index, Factor factor) {
        this.index = index;
        this.factor = factor;

        if (this.index.compareTo(ExprCheck.tenThousand) > 0) {
            ExprCheck.formatError();
        }
    }

    public SinFactor(String string, String exprFactor) {
        ExprCheck.checkSinFactor(string);
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

        ConstFactor newCoef = new ConstFactor(this.index); // b
        // sin(factor)^b-1
        SinFactor newSinFactor = new SinFactor(newIndex, factor);
        // cos(factor)
        CosFactor newCosFactor = new CosFactor(BigInteger.ONE, factor);
        Term diffedFactor = factor.diff(); // factor'
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
            res = "sin(" + factor.toString() + ")";
        } else {
            res = "sin(" + factor.toString() + ")^" + index.toString();
        }

        return res;
    }
}
