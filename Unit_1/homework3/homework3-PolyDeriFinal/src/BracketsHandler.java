import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

public class BracketsHandler {
    /**
     * Normal brackets matching
     *
     * @param str
     * @return
     */
    public static boolean isMatch(String str) {
        // pair以右括号为key, 左括号为值
        Map<Character, Character> pair = new HashMap<Character, Character>();
        pair.put(')', '(');
        pair.put(']', '[');

        Stack<Character> sc = new Stack<Character>();
        for (int i = 0; i < str.length(); i++) {
            Character ch = str.charAt(i);
            if (pair.containsValue(ch)) {
                sc.push(ch);
            } else if (pair.containsKey(ch)) {
                if (sc.empty()) {
                    return false;
                }
                // 栈不为空，栈头字符与右括号匹配
                if (sc.peek() == pair.get(ch)) {
                    sc.pop();
                } else {
                    return false;
                }
            }
        }

        if (sc.empty()) {
            return true;
        } else {
            return false;
        }
        //return sc.empty() ? true : false;
    }

    /**
     * extract expression in "()"
     * and ensure that the brackets are the outermost layer
     * e.g. getExpr("( sin(x) + cos(x) ) +   ....")
     * return "sin(x) + cos(x)";
     *
     * @param str
     * @return
     */
    public static String getExpr(String str) {
        Stack<Character> sc = new Stack<Character>();
        for (int i = 0; i < str.length(); i++) {
            Character ch = str.charAt(i);
            if (ch == '(') {
                sc.push(ch);            // push '('
            } else if (ch == ')') {     // pop if meet ')'
                sc.pop();
                if (sc.empty()) {
                    return str.substring(1, i);
                }
            }
        }
        // Actually, the program cannot execute to this line
        return "";
    }
}
