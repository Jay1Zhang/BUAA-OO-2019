import com.oocourse.elevator2.ElevatorInput;
import com.oocourse.elevator2.PersonRequest;

public class TestInput {
    public static void main(String[] args) throws Exception {
        ElevatorInput elevatorInput = new ElevatorInput(System.in);

        while(true) {
            PersonRequest request = elevatorInput.nextPersonRequest();
            if (request == null) {
                elevatorInput.close();
                return;
            }

            System.out.println(request);
        }
    }
}
