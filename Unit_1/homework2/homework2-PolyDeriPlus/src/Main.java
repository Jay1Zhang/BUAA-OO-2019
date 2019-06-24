import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        try {
            Scanner input = new Scanner(System.in);
            String str = input.nextLine();
            Polynomial poly = new Polynomial(str);
            Polynomial newPoly = poly.derivation();
            //System.out.println(poly.toString());
            System.out.println(newPoly.toString());
        } catch (Exception e) {
            System.out.println("WRONG FORMAT!");
            System.exit(0);
        }

    }
}
