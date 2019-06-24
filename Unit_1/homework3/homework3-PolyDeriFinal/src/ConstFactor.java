import java.math.BigInteger;

public class ConstFactor extends Factor {
    private BigInteger coef;

    public ConstFactor(BigInteger coef) {
        this.coef = coef;
    }

    public ConstFactor(String str) {
        ExprCheck.checkConstFactor(str);
        this.coef = new BigInteger(str);
    }

    public BigInteger getCoef() {
        return coef;
    }

    @Override
    public BigInteger getIndex() {
        return BigInteger.ONE;
    }

    @Override
    public Term diff() {
        return new Term("0");
    }

    @Override
    public String toString() {
        return this.coef.toString();
    }

    /*
    public ConstFactor mul(ConstFactor constFactor) {
        BigInteger newCoef = constFactor.getCoef().multiply(this.coef);
        return new ConstFactor(newCoef);
    }
    */
}
