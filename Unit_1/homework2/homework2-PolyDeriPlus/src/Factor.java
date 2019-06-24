import java.math.BigInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Factor {
    public static final String op = "[+-]?\\s*[+-]?\\s*";
    public static final String simpleX = "x";
    public static final String generalX = "x\\s*\\^\\s*[+-]?\\d+";
    public static final String simpleSinx = "sin\\s*\\(\\s*x\\s*\\)";
    public static final String simpleCosx = "cos\\s*\\(\\s*x\\s*\\)";
    public static final String genneralSinx =
            "sin\\s*\\(\\s*x\\s*\\)\\s*\\^\\s*[+-]?\\d+";
    public static final String genneralCosx =
            "cos\\s*\\(\\s*x\\s*\\)\\s*\\^\\s*[+-]?\\d+";
    public static final String signedNum = "[+-]?\\d+";

    private int form;
    private BigInteger index;
    private BigInteger coef;

    public Factor(int form, BigInteger index, BigInteger coef) {
        this.form = form;
        this.index = index;
        this.coef = coef;
    }

    public Factor(String string) {
        String str = string.trim();

        Pattern p0 = Pattern.compile(signedNum);
        Matcher m0 = p0.matcher(str);
        Pattern p1 = Pattern.compile(simpleX);
        Matcher m1 = p1.matcher(str);
        Pattern p2 = Pattern.compile(generalX);
        Matcher m2 = p2.matcher(str);
        Pattern p3 = Pattern.compile(simpleSinx);
        Matcher m3 = p3.matcher(str);
        Pattern p4 = Pattern.compile(genneralSinx);
        Matcher m4 = p4.matcher(str);
        Pattern p5 = Pattern.compile(simpleCosx);
        Matcher m5 = p5.matcher(str);
        Pattern p6 = Pattern.compile(genneralCosx);
        Matcher m6 = p6.matcher(str);

        if (m0.matches()) {
            str = str.replaceAll("\\s", "");
            form = 0;
            index = BigInteger.ZERO;
            coef = new BigInteger(str);
        } else if (m1.matches()) {
            form = 1;
            index = BigInteger.ONE;
            coef = BigInteger.ONE;
        } else if (m2.matches()) {
            str = str.replaceAll("\\s", "");
            form = 1;
            String ind = str.substring(str.indexOf('^') + 1);
            index = new BigInteger(ind);
            coef = BigInteger.ONE;
        } else if (m3.matches()) {
            form = 2;
            index = BigInteger.ONE;
            coef = BigInteger.ONE;
        } else if (m4.matches()) {
            str = str.replaceAll("\\s", "");
            form = 2;
            String ind = str.substring(str.indexOf('^') + 1);
            index = new BigInteger(ind);
            coef = BigInteger.ONE;
        } else if (m5.matches()) {
            form = 3;
            index = BigInteger.ONE;
            coef = BigInteger.ONE;
        } else if (m6.matches()) {
            str = str.replaceAll("\\s", "");
            form = 3;
            String ind = str.substring(str.indexOf('^') + 1);
            index = new BigInteger(ind);
            coef = BigInteger.ONE;
        } else {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }

        if (form != 0 && index.equals(BigInteger.ZERO)) {
            form = 0;
            index = BigInteger.ZERO;
            coef = BigInteger.ONE;
        }
    }

    public Factor(String string, boolean isFirst) {
        String str = string.trim();

        Pattern p0 = Pattern.compile(op + signedNum);
        Matcher m0 = p0.matcher(str);
        Pattern p1 = Pattern.compile(op + simpleX);
        Matcher m1 = p1.matcher(str);
        Pattern p2 = Pattern.compile(op + generalX);
        Matcher m2 = p2.matcher(str);
        Pattern p3 = Pattern.compile(op + simpleSinx);
        Matcher m3 = p3.matcher(str);
        Pattern p4 = Pattern.compile(op + genneralSinx);
        Matcher m4 = p4.matcher(str);
        Pattern p5 = Pattern.compile(op + simpleCosx);
        Matcher m5 = p5.matcher(str);
        Pattern p6 = Pattern.compile(op + genneralCosx);
        Matcher m6 = p6.matcher(str);

        if (m0.matches()) {
            str = replaceOp(str);

            form = 0;
            index = BigInteger.ZERO;
            coef = new BigInteger(str);
        } else if (m1.matches()) {
            str = replaceOp(str);

            form = 1;
            index = BigInteger.ONE;
            if (str.charAt(0) == '-') {
                coef = BigInteger.valueOf(-1);
            } else {
                coef = BigInteger.ONE;
            }

        } else if (m2.matches()) {
            str = replaceOp(str);

            form = 1;
            String ind = str.substring(str.indexOf('^') + 1);
            index = new BigInteger(ind);
            if (str.charAt(0) == '-') {
                coef = BigInteger.valueOf(-1);
            } else {
                coef = BigInteger.ONE;
            }
        } else if (m3.matches()) {
            str = replaceOp(str);

            form = 2;
            index = BigInteger.ONE;
            if (str.charAt(0) == '-') {
                coef = BigInteger.valueOf(-1);
            } else {
                coef = BigInteger.ONE;
            }
        } else if (m4.matches()) {
            str = replaceOp(str);

            form = 2;
            String ind = str.substring(str.indexOf('^') + 1);
            index = new BigInteger(ind);
            if (str.charAt(0) == '-') {
                coef = BigInteger.valueOf(-1);
            } else {
                coef = BigInteger.ONE;
            }
        } else if (m5.matches()) {
            str = replaceOp(str);

            form = 3;
            index = BigInteger.ONE;
            if (str.charAt(0) == '-') {
                coef = BigInteger.valueOf(-1);
            } else {
                coef = BigInteger.ONE;
            }
        } else if (m6.matches()) {
            str = replaceOp(str);

            form = 3;
            String ind = str.substring(str.indexOf('^') + 1);
            index = new BigInteger(ind);
            if (str.charAt(0) == '-') {
                coef = BigInteger.valueOf(-1);
            } else {
                coef = BigInteger.ONE;
            }
        } else {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }

    }

    public int getForm() {
        return form;
    }

    public BigInteger getIndex() {
        return index;
    }

    public BigInteger getCoef() {
        return coef;
    }

    private String replaceOp(String string) {
        String str = string.replaceAll("\\s", "");

        str = str.replaceAll("\\+\\+\\+", "+");
        str = str.replaceAll("\\+\\+\\-", "-");
        str = str.replaceAll("\\+\\-\\+", "-");
        str = str.replaceAll("\\+\\-\\-", "+");
        str = str.replaceAll("\\-\\+\\+", "-");
        str = str.replaceAll("\\-\\+\\-", "+");
        str = str.replaceAll("\\-\\-\\+", "+");
        str = str.replaceAll("\\-\\-\\-", "-");

        str = str.replaceAll("\\+\\+", "+");
        str = str.replaceAll("\\+\\-", "-");
        str = str.replaceAll("\\-\\+", "-");
        str = str.replaceAll("\\-\\-", "+");
        return str;
    }

    protected Factor derivation() {
        Factor res;
        int form;
        BigInteger index;
        BigInteger coef;
        switch (this.form) {
            case 0:
                form = 0;
                index = BigInteger.ZERO;
                coef = BigInteger.ZERO;
                break;
            case 1:
                if (this.index.equals(BigInteger.ONE)) {
                    form = 0;
                    index = BigInteger.ZERO;
                    coef = this.coef;
                } else {
                    form = 1;
                    index = this.index.subtract(BigInteger.ONE);
                    coef = this.coef.multiply(this.index);
                }
                break;
            case 2:
                form = 3;
                if (this.index.equals(BigInteger.ONE)) {
                    index = BigInteger.ONE;
                } else {
                    index = this.index.subtract(BigInteger.ONE);
                }
                coef = this.coef.multiply(this.index);
                break;
            case 3:
                form = 2;
                if (this.index.equals(BigInteger.ONE)) {
                    index = BigInteger.ONE;
                } else {
                    index = this.index.subtract(BigInteger.ONE);
                }
                coef = this.coef.multiply(this.index).
                        multiply(BigInteger.valueOf(-1));
                break;
            default:
                form = -1;
                index = null;
                coef = null;
                break;
        }
        res = new Factor(form, index, coef);

        return res;
    }

}
