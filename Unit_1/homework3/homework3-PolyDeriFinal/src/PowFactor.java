import java.math.BigInteger;

public class PowFactor extends Factor {
    private BigInteger index;

    public PowFactor(String string) {
        ExprCheck.checkPowFactor(string);
        if (string.contains("^")) {
            String str = string.substring(string.indexOf('^') + 1);
            ExprCheck.checkConstFactor(str);
            this.index = new BigInteger(str);
        } else {
            this.index = BigInteger.ONE;
        }

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

        if (newIndex.equals(BigInteger.ZERO)) {
            newTerm = new Term("1");
        } else {
            String temp = "x^" + newIndex.toString();
            PowFactor powFactor = new PowFactor(temp);
            ConstFactor constFactor = new ConstFactor(this.index);
            // newTerm = new Term(temp);
            newTerm.addFactor(powFactor);
            newTerm.addFactor(constFactor);
        }

        return newTerm;
    }

    @Override
    public String toString() {
        String res = new String();
        if (index.equals(BigInteger.ZERO)) {
            res = "1";
        } else if (index.equals(BigInteger.ONE)) {
            res = "x";
        } else {
            res = "x^" + this.index.toString();
        }

        return res;
    }
}
