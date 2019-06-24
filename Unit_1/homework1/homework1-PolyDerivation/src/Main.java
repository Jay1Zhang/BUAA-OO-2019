import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        Scanner input = new Scanner(System.in);
        String str = input.nextLine();
        Polynomial poly = new Polynomial(str);
        Polynomial newPoly = poly.derivation();

        System.out.println(newPoly.toString());

    }
}
