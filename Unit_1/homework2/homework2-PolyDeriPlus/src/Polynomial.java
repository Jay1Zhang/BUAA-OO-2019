import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Polynomial {
    private HashMap<MyList, Monomial> poly;

    public Polynomial() {
        poly = new HashMap<MyList, Monomial>();
    }

    public Polynomial(String string) {
        Pattern p0 = Pattern.compile("^[-+*x^ \t\\dcosin\\(\\)]+$");
        Matcher m0 = p0.matcher(string);
        if (!m0.matches()) {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }
        String str = string.trim();
        poly = new HashMap<MyList, Monomial>();
        StringBuffer sb = new StringBuffer();
        Pattern p1 = Pattern.compile("[x\\d\\)]\\s*[+-]");
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
        BigInteger k = item.getK();
        BigInteger a = item.getA();
        BigInteger b = item.getBbb();
        BigInteger c = item.getC();
        MyList list = new MyList(a, b, c);
        if (k.equals(BigInteger.ZERO)) {
            return;
        }
        if (poly.containsKey(list)) {
            BigInteger oldCoef = poly.get(list).getK();
            BigInteger newCoef = oldCoef.add(k);
            Monomial temp = new Monomial(newCoef, a, b, c);

            poly.put(list, temp);
        } else {
            poly.put(list, item);
        }
    }

    public ArrayList<Monomial> getPoly() {
        ArrayList<Monomial> myLists = new ArrayList<Monomial>();
        for (MyList key : poly.keySet()) {
            Monomial temp = poly.get(key);
            myLists.add(temp);
        }
        return myLists;
    }

    protected void addPoly(Polynomial polynomial) {
        ArrayList<Monomial> myLists = polynomial.getPoly();

        for (int i = 0; i < myLists.size(); i++) {
            this.addItem(myLists.get(i));
        }
    }

    public Polynomial derivation() {
        Polynomial newPoly = new Polynomial();
        for (MyList key : poly.keySet()) {
            Polynomial temp = poly.get(key).derivation();
            newPoly.addPoly(temp);
        }
        return newPoly;
    }

    public String toString() {
        String s = new String();
        for (MyList key : poly.keySet()) {
            String temp = poly.get(key).toString();
            if (temp.equals("")) {
                continue;
            }
            if (temp.charAt(0) != '-') {
                s = "+" + temp + s;
            } else {
                s += temp;
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
