import java.math.BigInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ExprCheck {
    /*
    public static final BigInteger tenThousand = BigInteger.valueOf(10000);
    public static final String op = "[+-]?\\s*[+-]?\\s*";
    public static final String signedNum = "[+-]?\\d+";
    public static final String generalX = "x(\\s*\\^\\s*[+-]?\\d+)?";
    public static final String genneralSinx =
            "sin\\s*\\(expr\\)(\\s*\\^\\s*[+-]?\\d+)?";
    public static final String genneralCosx =
            "cos\\s*\\(expr\\)(\\s*\\^\\s*[+-]?\\d+)?";
    public static final String generalExpr = "\\(expr\\)";
    */
    public static final BigInteger tenThousand = BigInteger.valueOf(10000);
    public static final String validChars = "^[-+*^ \t\\dcosinx\\(\\)]+$";
    public static final String numFormat = "(\\s*[+-]?\\d+\\s*)";
    public static final String xFormat = "(\\s*x\\s*(\\^\\s*[+-]?\\d+)?\\s*)";
    public static final String sinFormat =
            "(\\s*sin\\s*\\(.+\\)\\s*(\\^\\s*[+-]?\\d+)?\\s*)";
    public static final String cosFormat =
            "(\\s*cos\\s*\\(.+\\)\\s*(\\^\\s*[+-]?\\d+)?\\s*)";
    public static final String exprFormat = "(\\s*\\(.+\\)\\s*)";
    public static final String factorFormat =
            "(" + numFormat + "|" + xFormat + "|"
                    + sinFormat + "|" + cosFormat + "|" + exprFormat + ")";

    public static final String termFormat = "(" + "([-+]\\s*)?" + factorFormat
            + "(\\s*\\*\\s*" + factorFormat + ")*" + ")";
    public static final String Expr = "^[-+]?\\s*" + termFormat
            + "(\\s*[-+]\\s*" + termFormat + ")*$";

    public static void formatCheck(String str) {
        // 首先扫描输入串str, 检查是否为空串或是否包含非法字符
        Pattern p = Pattern.compile(validChars);
        Matcher m = p.matcher(str);
        if (!m.matches()) {
            formatError();
        }
        // 判断括号是否匹配
        if (!BracketsHandler.isMatch(str)) {
            formatError();
        }
        // 对expr作最终审查
        Pattern p1 = Pattern.compile(Expr);
        Matcher m1 = p1.matcher(str.trim());
        if (!m1.matches()) {
            formatError();
        }
        //System.out.println("Input Valid!");
    }

    public static String replaceOp(String string) {
        String str = string.replaceAll("\\s", "");
        // op三连 - if
        str = str.replaceAll("\\+\\+\\+", "+");
        str = str.replaceAll("\\+\\+\\-", "-");
        str = str.replaceAll("\\+\\-\\+", "-");
        str = str.replaceAll("\\+\\-\\-", "+");
        str = str.replaceAll("\\-\\+\\+", "-");
        str = str.replaceAll("\\-\\+\\-", "+");
        str = str.replaceAll("\\-\\-\\+", "+");
        str = str.replaceAll("\\-\\-\\-", "-");
        // op二连
        str = str.replaceAll("\\+\\+", "+");
        str = str.replaceAll("\\+\\-", "-");
        str = str.replaceAll("\\-\\+", "-");
        str = str.replaceAll("\\-\\-", "+");

        return str;
    }

    public static void checkConstFactor(String string) {
        Pattern p = Pattern.compile(numFormat);
        Matcher m = p.matcher(string);
        if (!m.matches()) {
            formatError();
        }
    }

    public static void checkPowFactor(String string) {
        Pattern p = Pattern.compile(xFormat);
        Matcher m = p.matcher(string);
        if (!m.matches()) {
            formatError();
        }
    }

    public static void checkSinFactor(String string) {
        Pattern p = Pattern.compile(sinFormat);
        Matcher m = p.matcher(string);
        if (!m.matches()) {
            formatError();
        }
    }

    public static void checkCosFactor(String string) {
        Pattern p = Pattern.compile(cosFormat);
        Matcher m = p.matcher(string);
        if (!m.matches()) {
            formatError();
        }
    }

    public static void checkExprFactor(String string) {
        Pattern p = Pattern.compile(exprFormat);
        Matcher m = p.matcher(string);
        if (!m.matches()) {
            formatError();
        }
    }

    public static void checkFactor(String string) {
        String str = string.trim();

        Pattern p = Pattern.compile(factorFormat);
        Matcher m = p.matcher(str);
        if (!m.matches()) {
            formatError();
        }
    }

    public static int whatFactor(String string) {
        String str = string.trim();

        Pattern p0 = Pattern.compile(numFormat);
        Matcher m0 = p0.matcher(str);

        Pattern p1 = Pattern.compile(xFormat);
        Matcher m1 = p1.matcher(str);

        Pattern p2 = Pattern.compile(sinFormat);
        Matcher m2 = p2.matcher(str);

        Pattern p3 = Pattern.compile(cosFormat);
        Matcher m3 = p3.matcher(str);

        Pattern p4 = Pattern.compile(exprFormat);
        Matcher m4 = p4.matcher(str);

        if (m0.matches()) {
            return 0;
        } else if (m1.matches()) {
            return 1;
        } else if (m2.matches()) {
            return 2;
        } else if (m3.matches()) {
            return 3;
        } else if (m4.matches()) {
            return 4;
        } else {
            formatError();
        }
        return -1;
    }

    public static void formatError() {
        System.out.println("WRONG FORMAT!");
        System.exit(0);
    }
}
