import com.oocourse.elevator3.PersonRequest;
import oocourse.elevator3.data.Request;

public class TestRequest {
    public static void main(String[] args) {
        PersonRequest personRequest = new PersonRequest(3, -2, 110);
        Request request = new Request(personRequest);

        if (request.hasChildRqst()) {
            System.out.println("This request: " + personRequest + "has to transfer to another elevator.");
            System.out.println("mainRqst: " + request);
            System.out.println("main optional EleId is " + request.getOptEleStr());
            request.changeMainRqst();
            System.out.println("childRqst: " + request);
            System.out.println("child optional EleId is " + request.getOptEleStr());
        } else {
            System.out.println("This request: " + personRequest + " is nonstop.");
            System.out.println("mainRqst: " + request);
            System.out.println("main optional EleId is " + request.getOptEleStr());
        }

    }
}
