import java.math.BigInteger;

public class Monomial {
    private BigInteger kkk = BigInteger.ONE;
    private BigInteger aaa = BigInteger.ZERO;
    private BigInteger bbb = BigInteger.ZERO;
    private BigInteger ccc = BigInteger.ZERO;

    public Monomial(BigInteger k, BigInteger a, BigInteger b, BigInteger c) {
        this.kkk = k;
        this.aaa = a;
        this.bbb = b;
        this.ccc = c;
    }

    public Monomial(String str) {
        String[] strs = str.split("\\*");
        if (str.charAt(str.length() - 1) == '*') {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }

        for (int i = 0; i < strs.length; i++) {
            Factor temp;
            if (i == 0) {
                temp = new Factor(strs[i], true);
            } else {
                temp = new Factor(strs[i]);
            }
            this.addFactor(temp);
        }

    }

    private void addFactor(Factor factor) {
        switch (factor.getForm()) {
            case 0:
                kkk = kkk.multiply(factor.getCoef());
                break;
            case 1:
                kkk = kkk.multiply(factor.getCoef());
                aaa = aaa.add(factor.getIndex());
                break;
            case 2:
                kkk = kkk.multiply(factor.getCoef());
                bbb = bbb.add(factor.getIndex());
                break;
            case 3:
                kkk = kkk.multiply(factor.getCoef());
                ccc = ccc.add(factor.getIndex());
                break;
            default:
                System.out.println("WRONG FORMAT!");
                System.exit(0);
        }
    }

    public BigInteger getK() {
        return kkk;
    }

    public BigInteger getA() {
        return aaa;
    }

    public BigInteger getBbb() {
        return bbb;
    }

    public BigInteger getC() {
        return ccc;
    }

    protected Polynomial derivation() {
        Monomial item1 = new Monomial(this.kkk.multiply(this.aaa),
                this.aaa.subtract(BigInteger.ONE), this.bbb, this.ccc);
        Monomial item2 = new Monomial(this.kkk.multiply(this.bbb),
                this.aaa, this.bbb.subtract(BigInteger.ONE),
                this.ccc.add(BigInteger.ONE));
        Monomial item3 = new Monomial(
                this.kkk.multiply(this.ccc).multiply(BigInteger.valueOf(-1)),
                this.aaa, this.bbb.add(BigInteger.ONE),
                this.ccc.subtract(BigInteger.ONE));

        Polynomial res = new Polynomial();
        res.addItem(item1);
        res.addItem(item2);
        res.addItem(item3);

        return res;
    }

    public String toString() {
        String s = new String();
        boolean flagA = !aaa.equals(BigInteger.ZERO);
        boolean flagB = !bbb.equals(BigInteger.ZERO);
        boolean flagC = !ccc.equals(BigInteger.ZERO);
        if (kkk.equals(BigInteger.ZERO)) {
            return "";
        }
        if (!flagA & !flagB & !flagC) {
            s += kkk.toString();
        } else {
            if (kkk.equals(BigInteger.ONE)) {
                // There is nothing to do
            } else if (kkk.equals(BigInteger.valueOf(-1))) {
                s += "-";
            } else {
                s += kkk.toString() + "*";
            }

            if (!flagA & !flagB & flagC) {
                s += "cos(x)^" + ccc.toString();
            } else if (!flagA & flagB & !flagC) {
                s += "sin(x)^" + bbb.toString();
            } else if (!flagA & flagB & flagC) {
                s += "sin(x)^" + bbb.toString() + "*cos(x)^" + ccc.toString();
            } else if (flagA & !flagB & !flagC) {
                s += "x^" + aaa.toString();
            } else if (flagA & !flagB & flagC) {
                s += "x^" + aaa.toString() + "*cos(x)^" + ccc.toString();
            } else if (flagA & flagB & !flagC) {
                s += "x^" + aaa.toString() + "*sin(x)^" + bbb.toString();
            } else if (flagA & flagB & flagC) {
                s += "x^" + aaa.toString() + "*sin(x)^" + bbb.toString()
                        + "*cos(x)^" + ccc.toString();
            } else {
                System.out.println("WRONG FORMAT!");
                System.exit(0);
            }
        }
        s += "*";
        s = s.replaceAll("\\^1\\*", "*");
        s = s.substring(0, s.length() - 1);
        return s;
    }
}
