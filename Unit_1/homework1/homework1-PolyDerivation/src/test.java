import java.util.Scanner;

public class test {
    public static void main(String[] args) {
        /*
        Scanner input = new Scanner(System.in);
        //String str = "   -1 *x+-x   -  2*x^6  +-5*x^  -3 --8   ";

        while (true) {
            String str = input.nextLine();
            Polynomial poly = new Polynomial(str);
            Polynomial newPoly = poly.derivation();
            System.out.println(poly.toString());
            System.out.println(newPoly.toString());
        }
        */
        /*
        String str = " -1";
        Polynomial poly = new Polynomial(str);
        Polynomial newPoly = poly.derivation();
        System.out.println(poly.toString());
        System.out.println(newPoly.toString());
        */

        String str = "";
        for (int i = 0; i < 512; i++){
            str += "+x";
        }
        System.out.println(str);

    }
}
