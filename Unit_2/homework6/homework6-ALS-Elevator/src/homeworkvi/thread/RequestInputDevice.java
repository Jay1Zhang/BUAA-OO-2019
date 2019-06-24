package homeworkvi.thread;

import com.oocourse.elevator2.ElevatorInput;
import com.oocourse.elevator2.PersonRequest;
import homeworkvi.data.RequestQueue;

public class RequestInputDevice extends Thread {
    private final RequestQueue requestQueue;

    public RequestInputDevice(RequestQueue requestQueue) {
        super("RequestInputDevice");
        this.requestQueue = requestQueue;
    }

    public void run() {
        try {
            ElevatorInput elevatorInput = new ElevatorInput(System.in);

            while (true) {
                PersonRequest request = elevatorInput.nextPersonRequest();
                // when request == null
                // it means there are no more lines in stdin
                if (request == null) {
                    requestQueue.setEndTag(true);
                    break;
                } else {
                    // a new valid request
                    requestQueue.putRequest(request);
                }
            }
            elevatorInput.close();
            //TimableOutput.println(currentThread().getName() + " end");
        } catch (Exception e) {
            // print something else
            e.printStackTrace();
        }

    }
}
