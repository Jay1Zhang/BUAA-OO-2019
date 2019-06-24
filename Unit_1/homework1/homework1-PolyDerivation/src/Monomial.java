import java.math.BigInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Monomial {
    private BigInteger index;
    private BigInteger coefficient;

    public Monomial() {
        index = null;
        coefficient = null;
    }

    public Monomial(BigInteger index, BigInteger coefficient) {
        this.index = index;
        this.coefficient = coefficient;
    }

    public Monomial(String string) {
        String str = string;
        str = str.trim();

        String regex = "^[+-]?\\s*[+-]?\\d+\\s*\\*\\s*x\\s*" +
                "\\^\\s*[+-]?\\d+$";
        String regex1 = "^[+-]?\\s*[+-]?\\s*x\\s*\\^\\s*[+-]?\\d+$";
        String regex2 = "^[+-]?\\s*[+-]?\\d+\\s*\\*\\s*x$";
        String regex3 = "^[+-]?\\s*[+-]?\\s*x$";
        String regex4 = "^[+-]?\\s*[+-]?\\d+$";


        Pattern p = Pattern.compile(regex);
        Matcher m = p.matcher(str);

        Pattern p1 = Pattern.compile(regex1);
        Matcher m1 = p1.matcher(str);

        Pattern p2 = Pattern.compile(regex2);
        Matcher m2 = p2.matcher(str);

        Pattern p3 = Pattern.compile(regex3);
        Matcher m3 = p3.matcher(str);

        Pattern p4 = Pattern.compile(regex4);
        Matcher m4 = p4.matcher(str);

        if (m.matches()) {               // 2*x^2
            str = str.replaceAll("\\s", "");
            str = str.replaceAll("(\\+\\+)|(--)", "+");
            str = str.replaceAll("(\\+-)|(-\\+)", "-");
            String[] strs = str.split("[*^]");

            index = new BigInteger(strs[strs.length - 1]);
            coefficient = new BigInteger(strs[0]);
        } else if (m1.matches()) {        // x^2
            str = str.replaceAll("\\s", "");
            str = str.replaceAll("(\\+\\+)|(--)", "+");
            str = str.replaceAll("(\\+-)|(-\\+)", "-");
            String[] strs = str.split("[x^]");

            index = new BigInteger(strs[strs.length - 1]);
            if (strs[0].equals("-")) {
                coefficient = new BigInteger("-1");
            } else {
                coefficient = new BigInteger("1");
            }
        } else if (m2.matches()) {        // 2*x
            str = str.replaceAll("\\s", "");
            str = str.replaceAll("(\\+\\+)|(--)", "+");
            str = str.replaceAll("(\\+-)|(-\\+)", "-");
            String[] strs = str.split("[*x]");

            index = new BigInteger("1");
            coefficient = new BigInteger(strs[0]);
        } else if (m3.matches()) {        // +x -x
            str = str.replaceAll("\\s", "");
            str = str.replaceAll("(\\+\\+)|(--)", "+");
            str = str.replaceAll("(\\+-)|(-\\+)", "-");
            boolean isNegative = str.charAt(0) == '-';

            index = new BigInteger("1");
            if (isNegative) {
                coefficient = new BigInteger("-1");
            } else {
                coefficient = new BigInteger("1");
            }
        } else if (m4.matches()) {        // -1
            str = str.replaceAll("\\s", "");
            str = str.replaceAll("(\\+\\+)|(--)", "+");
            str = str.replaceAll("(\\+-)|(-\\+)", "-");
            index = new BigInteger("0");
            coefficient = new BigInteger(str);
        } else {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }
    }

    protected BigInteger getIndex() {
        return index;
    }

    protected BigInteger getCoefficient() {
        return coefficient;
    }

    protected Monomial derivation() {
        BigInteger coef = this.coefficient.multiply(this.index);
        BigInteger ind;
        if (this.index.equals(BigInteger.ZERO) | coef.equals(BigInteger.ZERO)) {
            ind = BigInteger.ZERO;
        } else {
            ind = this.index.subtract(BigInteger.ONE);
        }

        Monomial temp = new Monomial(ind, coef);

        return temp;
    }
}
