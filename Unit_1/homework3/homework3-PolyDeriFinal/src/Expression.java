import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Expression {
    private ArrayList<Term> terms;
    private ArrayList<String> exprs;
    private int counter = 0;

    public Expression() {
        terms = new ArrayList<Term>();
        exprs = new ArrayList<String>();
    }

    public Expression(String string) {
        this();
        // 0. 字符串预处理
        ExprCheck.formatCheck(string);              // 格式检查
        String str = ExprCheck.replaceOp(string);   // 消除空白符以及替换连续的操作符
        // 1. Replace
        str = ExprReplace(str);                     // 将括号内替换为(E)并存储到exprs
        // 2. 将多项式分割为若干个单项
        StringBuffer sb = new StringBuffer();
        Pattern p = Pattern.compile("[x\\d\\)]\\s*[+-]");
        Matcher m = p.matcher(str);
        while (m.find()) {
            StringBuffer temp = new StringBuffer(m.group());
            temp.insert(1, "@");
            m.appendReplacement(sb, temp.toString());
        }
        m.appendTail(sb);
        str = sb.toString();
        // 3. 逐个构造单项式
        String[] strs = str.split("@");
        for (int i = 0; i < strs.length; i++) {
            ArrayList<String> exprList = getExprList(strs[i]);
            Term item = new Term(strs[i], exprList);

            this.addItem(item);
        }
    }

    private String ExprReplace(String str) {
        StringBuffer sb = new StringBuffer();
        for (int i = 0; i < str.length(); i++) {
            Character ch = str.charAt(i);
            if (ch == '(') {
                String exprStr = BracketsHandler.getExpr(str.substring(i));

                exprs.add(exprStr);
                sb.append("(E)");
                i += exprStr.length() + 2 - 1;
            } else {
                sb.append(ch);
            }
        }
        return sb.toString();
    }

    private ArrayList<String> getExprList(String str) {
        ArrayList<String> exprList = new ArrayList<String>();
        Pattern p = Pattern.compile("\\(E\\)");
        Matcher m = p.matcher(str);
        while (m.find()) {
            String expr = exprs.get(counter++);
            exprList.add(expr);
        }

        return exprList;
    }

    private void addItem(Term item) {
        terms.add(item);
    }

    private void addTerms(ArrayList<Term> termArrayList) {
        this.terms.addAll(termArrayList);
    }

    public Expression diff() {
        Expression newExpr = new Expression();

        for (int i = 0; i < terms.size(); i++) {
            ArrayList<Term> termsDiffed = new ArrayList<Term>();
            termsDiffed = terms.get(i).diff();
            newExpr.addTerms(termsDiffed);
        }

        return newExpr;
    }

    @Override
    public String toString() {
        String res = new String();

        for (int i = 0; i < terms.size(); i++) {
            String term = terms.get(i).toString();
            res += term + "+";
        }
        res = res.substring(0, res.length() - 1);

        return res;

    }
}
