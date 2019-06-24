import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;

public class Term {
    private ArrayList<Factor> factors;

    public Term() {
        factors = new ArrayList<Factor>();
    }

    public Term(String str) {
        this();
        // str必定为单个因子
        if (str.contains("x")) {
            PowFactor powFactor = new PowFactor(str);
            factors.add(powFactor);
        } else {
            ConstFactor constFactor = new ConstFactor(str);
            factors.add(constFactor);
        }

        //System.out.println("Term Constructer(String)");
    }

    public Term(String string, ArrayList<String> exprList) {
        this();

        Iterator<String> iter = exprList.iterator();
        String[] strs = string.split("\\*");
        for (int i = 0; i < strs.length; i++) {
            String str = strs[i];
            String expr;

            if (str.charAt(0) == '+') {
                ConstFactor factor = new ConstFactor("1");
                factors.add(factor);
                str = str.substring(1);
            } else if (str.charAt(0) == '-') {
                ConstFactor factor = new ConstFactor("-1");
                factors.add(factor);
                str = str.substring(1);
            }
            // 检索出各个因子，分别进行构建
            int form = ExprCheck.whatFactor(str);
            switch (form) {
                case 0:
                    ConstFactor factor0 = new ConstFactor(str);
                    factors.add(factor0);
                    break;
                case 1:
                    PowFactor factor1 = new PowFactor(str);
                    factors.add(factor1);
                    break;
                case 2:
                    if (str.contains("(E)") && iter.hasNext()) {
                        expr = iter.next();
                        SinFactor factor2 = new SinFactor(str, expr);
                        factors.add(factor2);
                    } else {
                        ExprCheck.formatError();
                    }
                    break;
                case 3:
                    if (str.contains("(E)") && iter.hasNext()) {
                        expr = iter.next();
                        CosFactor factor3 = new CosFactor(str, expr);
                        factors.add(factor3);
                    } else {
                        ExprCheck.formatError();
                    }

                    break;
                case 4:
                    if (str.contains("(E)") && iter.hasNext()) {
                        expr = iter.next();
                        ExprFactor factor4 = new ExprFactor(expr);
                        factors.add(factor4);
                    } else {
                        ExprCheck.formatError();
                    }

                    break;
                default:
                    ExprCheck.formatError();
            }
        }
    }

    public ArrayList<Term> diff() {
        ArrayList<Term> termList = new ArrayList<Term>();

        for (int i = 0; i < factors.size(); i++) {
            ArrayList<Factor> otherFactors = getOtherFactors(i);
            Term newTerm = factors.get(i).diff();
            for (int j = 0; j < otherFactors.size(); j++) {
                newTerm.addFactor(otherFactors.get(j));
            }
            termList.add(newTerm);
        }
        return termList;
    }

    private ArrayList<Factor> getOtherFactors(int index) {
        ArrayList<Factor> otherFactors = new ArrayList<Factor>();

        for (int i = 0; i < factors.size(); i++) {
            if (i == index) {
                continue;
            } else {
                Factor factor = factors.get(i);
                otherFactors.add(factor);
            }
        }
        return otherFactors;
    }

    public void addFactor(Factor factor) {
        if (factor.getIndex().equals(BigInteger.ZERO)) {
            return;
        } else {
            factors.add(factor);
        }
    }

    @Override
    public String toString() {
        String res = new String();

        for (int i = 0; i < factors.size(); i++) {
            String factor = factors.get(i).toString();
            if (factor.equals("0")) {
                return "0";
            }
            res += factor + "*";
        }
        res = res.substring(0, res.length() - 1);

        return res;
    }
}
