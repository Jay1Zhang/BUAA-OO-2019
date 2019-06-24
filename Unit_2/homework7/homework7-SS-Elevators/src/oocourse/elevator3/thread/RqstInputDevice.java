package oocourse.elevator3.thread;

import com.oocourse.elevator3.ElevatorInput;
import com.oocourse.elevator3.PersonRequest;
import oocourse.elevator3.data.Request;
import oocourse.elevator3.data.RequestQueue;

public class RqstInputDevice extends Thread {
    private final RequestQueue requestQueue;

    public RqstInputDevice(RequestQueue requestQueue) {
        super("Thread-RqstInputDevice");
        this.requestQueue = requestQueue;
    }

    @Override
    public void run() {
        try {
            ElevatorInput elevatorInput = new ElevatorInput(System.in);
            while (true) {
                PersonRequest personRequest = elevatorInput.nextPersonRequest();
                // when request == null
                // it means there are no more lines in stdin
                if (personRequest == null) {
                    requestQueue.setInputEndTag(true);
                    break;
                } else {
                    // a new valid request
                    Request request = new Request(personRequest);
                    requestQueue.putRequest(request);
                }
            }
            elevatorInput.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
        //TimableOutput.println(currentThread().getName() + " done.");
    }
}
