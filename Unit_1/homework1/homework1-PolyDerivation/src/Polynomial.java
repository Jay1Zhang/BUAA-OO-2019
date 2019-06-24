import java.math.BigInteger;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Polynomial {
    private HashMap<BigInteger, Monomial> poly;

    public Polynomial() {
        poly = new HashMap<BigInteger, Monomial>();
    }

    public Polynomial(String string) {
        String str = string;
        poly = new HashMap<BigInteger, Monomial>();

        str = str.trim();

        Pattern p0 = Pattern.compile("^[-+*x^ \t\\d]+$");
        Matcher m0 = p0.matcher(string);
        if (!m0.matches()) {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }

        StringBuffer sb = new StringBuffer();
        Pattern p1 = Pattern.compile("[x\\d]\\s*[+-]");
        Matcher m1 = p1.matcher(str);
        while (m1.find()) {
            StringBuffer temp = new StringBuffer(m1.group());
            temp.insert(1, "t");
            m1.appendReplacement(sb, temp.toString());
        }
        m1.appendTail(sb);
        str = sb.toString();

        String[] strs = str.split("t");
        for (int i = 0; i < strs.length; i++) {
            Monomial item = new Monomial(strs[i]);
            this.addItem(item);
        }
    }

    protected void addItem(Monomial item) {
        BigInteger index = item.getIndex();

        if (item.getCoefficient().equals(BigInteger.ZERO)) {
            return;
        }

        if (poly.containsKey(index)) {
            BigInteger oldCoef = poly.get(index).getCoefficient();
            BigInteger newCoef = oldCoef.add(item.getCoefficient());
            Monomial temp = new Monomial(index, newCoef);

            poly.put(index, temp);
        } else {
            poly.put(index, item);
        }
    }

    public Polynomial derivation() {
        Polynomial newPoly = new Polynomial();
        for (BigInteger key : poly.keySet()) {
            Monomial temp = poly.get(key).derivation();
            newPoly.addItem(temp);
        }

        return newPoly;
    }

    public String toString() {
        String s = new String();

        for (BigInteger key : poly.keySet()) {
            Monomial temp = poly.get(key);
            String index = temp.getIndex().toString();
            String coef = "";
            if (temp.getCoefficient().compareTo(BigInteger.ZERO) > 0) {
                coef = "+" + temp.getCoefficient().toString();
            } else if (temp.getCoefficient().compareTo(BigInteger.ZERO) < 0) {
                coef = temp.getCoefficient().toString();
            } else {
                coef += "";
            }

            if (index.equals("0")) {
                s += coef;
            } else if (index.equals("1")) {
                if (coef.equals("+1")) {
                    s += "+x";
                } else if (coef.equals("-1")) {
                    s += "-x";
                } else {
                    s += coef + "*x";
                }
            } else {
                if (coef.equals("+1")) {
                    s += "+x^" + index;
                } else if (coef.equals("-1")) {
                    s += "-x^" + index;
                } else {
                    s += coef + "*x^" + index;
                }
            }
        }
        if (s.equals("")) {
            return "0";
        } else if (s.charAt(0) == '+') {
            return (s.replaceFirst("\\+", ""));
        } else {
            return (s);
        }
    }

}
