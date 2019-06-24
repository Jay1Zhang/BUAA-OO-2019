import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        try {
            Scanner input = new Scanner(System.in);
            String str = input.nextLine();
            Expression expression = new Expression(str);
            //String expr = expression.toString();
            //System.out.println("expr:\t" + expr);
            String res = expression.diff().toString();
            System.out.println(res);
        } catch (Exception e) {
            ExprCheck.formatError();
        }

    }
}
