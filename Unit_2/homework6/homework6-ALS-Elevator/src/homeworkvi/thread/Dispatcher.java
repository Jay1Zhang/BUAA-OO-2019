package homeworkvi.thread;

import com.oocourse.elevator2.PersonRequest;
import homeworkvi.data.Constant.Status;
import homeworkvi.data.PiggybackQueue;
import homeworkvi.data.RequestQueue;

import java.util.ArrayList;
import java.util.Iterator;

public class Dispatcher {
    private final RequestQueue requestQueue;
    private final PiggybackQueue piggybackQueue;
    private Elevator elevator;

    public Dispatcher(RequestQueue requestQueue,
                      PiggybackQueue piggybackQueue,
                      Elevator elevator) {
        this.requestQueue = requestQueue;
        this.piggybackQueue = piggybackQueue;
        this.elevator = elevator;
    }

    public synchronized void updatePiggybackQueue() {
        int currentFloor = elevator.getCurrentFloor();
        Status currentStatus;
        Status viceStatus;

        elevator.resolveMainRequest();
        if (elevator.getStatus() == Status.WAIT) {
            // get main request and put in piggyback queue
            PersonRequest mainRequest = requestQueue.getRequest();

            if (mainRequest == null) {
                // time to end
                return;
            }

            piggybackQueue.putRequest(mainRequest);
            elevator.resolveMainRequest();
        }

        currentStatus = elevator.getStatus();

        ArrayList<PersonRequest> list = requestQueue.clone();
        for (Iterator<PersonRequest> iterator = list.iterator();
             iterator.hasNext();) {
            PersonRequest viceRequest = iterator.next();
            if (viceRequest.getFromFloor() < viceRequest.getToFloor()) {
                viceStatus = Status.UP;
            } else {
                viceStatus = Status.DOWN;
            }
            // get vice-requests and add to piggyback queue
            if (currentFloor == viceRequest.getFromFloor()
                    && viceStatus == currentStatus) {
                piggybackQueue.putRequest(viceRequest);
                requestQueue.remove(requestQueue.indexOf(viceRequest));
            }
        }

    }

}
