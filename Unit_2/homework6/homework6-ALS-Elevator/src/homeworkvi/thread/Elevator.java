package homeworkvi.thread;

import com.oocourse.TimableOutput;
import com.oocourse.elevator2.PersonRequest;
import homeworkvi.data.Passengers;
import homeworkvi.data.PiggybackQueue;
import homeworkvi.data.RequestQueue;

import java.util.ArrayList;
import java.util.Iterator;

import static homeworkvi.data.Constant.osDoorTime;
import static homeworkvi.data.Constant.Status;
import static homeworkvi.data.Constant.udMoveTime;

public class Elevator extends Thread {
    private final RequestQueue requestQueue;
    private final PiggybackQueue piggybackQueue;
    private final Passengers passengers;
    private Dispatcher dispatcher;
    private volatile Status status; // for now
    private volatile int currentFloor;

    public Elevator(RequestQueue requestQueue) {
        super("ElevatorThread");
        this.requestQueue = requestQueue;
        this.piggybackQueue = new PiggybackQueue();
        this.passengers = new Passengers();
        this.dispatcher = new Dispatcher(requestQueue, piggybackQueue, this);

        this.status = Status.WAIT;
        this.currentFloor = 1;
    }

    public void run() {
        // please MUST initialize start timestamp at the beginning
        TimableOutput.initStartTimestamp();
        try {
            while (true) {
                if (requestQueue.InputEnd()) {
                    if (piggybackQueue.isEmpty() && passengers.isEmpty()) {
                        break;
                    }
                }
                // 0. update queue
                dispatcher.updatePiggybackQueue();
                // 1. check if it's needed to open & close the door
                if (piggybackQueue.hasPiggyback(currentFloor)
                        || passengers.hasPassenger(currentFloor)) {
                    this.status = Status.OPEN;
                    TimableOutput.println("OPEN-" + this.currentFloor);
                    sleep(osDoorTime);  // ensure real-time

                    dispatcher.updatePiggybackQueue();
                    // 1.1 pick up sb.
                    takePassenger();
                    // 1.2 drop off sb.
                    sendPassenger();
                    // close the door
                    //sleep(osDoorTime);

                    this.status = Status.CLOSE;
                    TimableOutput.println("CLOSE-" + this.currentFloor);
                }
                // 2. resolve main request to update the status of elevator
                resolveMainRequest();
                // 3. move one level by current status
                move();

            }
            //TimableOutput.println(currentThread().getName() + " end.");
        } catch (Exception e) {
            e.printStackTrace();
        }

    }

    public Status getStatus() {
        return this.status;
    }

    public int getCurrentFloor() {
        return currentFloor;
    }

    public synchronized void resolveMainRequest() {
        PersonRequest mainRequest;
        // 如果电梯中有乘客，将其中到达时间最早的乘客请求作为主请求
        if (!passengers.isEmpty()) {
            mainRequest = passengers.getRequest(0);
            if (currentFloor < mainRequest.getToFloor()) {
                this.status = Status.UP;
            } else if (currentFloor > mainRequest.getToFloor()) {
                this.status = Status.DOWN;
            } else {
                // 有可能此时主请求刚被送到目的地
                // TimableOutput.println("ConfusingMainRequest - passengers");
            }
            return;
        }

        // 如果电梯中没有乘客，将请求队列中到达时间最早的请求作为主请求
        if (!piggybackQueue.isEmpty()) {
            mainRequest = piggybackQueue.getRequest(0);
            if (currentFloor < mainRequest.getFromFloor()) {
                this.status = Status.UP;
            } else if (currentFloor > mainRequest.getFromFloor()) {
                this.status = Status.DOWN;
            } else {    // =
                //TimableOutput.println("ConfusingMainRequest - piggyback");
                if (currentFloor < mainRequest.getToFloor()) {
                    this.status = Status.UP;
                } else {
                    this.status = Status.DOWN;
                }
            }
            return;
        }

        // if there is nothing to do, WAIT
        this.status = Status.WAIT;
    }

    private void takePassenger() {
        ArrayList<PersonRequest> list = piggybackQueue.clone();
        for (Iterator<PersonRequest> iterator = list.iterator();
             iterator.hasNext();) {
            PersonRequest request = iterator.next();

            if (request.getFromFloor() == currentFloor) {
                passengers.putRequest(request);
                piggybackQueue.remove(piggybackQueue.indexOf(request));
                TimableOutput.println(
                        "IN-" + request.getPersonId() + "-" + currentFloor);
            }
        }

    }

    private void sendPassenger() {
        ArrayList<PersonRequest> list = passengers.clone();
        for (Iterator<PersonRequest> iterator = list.iterator();
             iterator.hasNext();) {
            PersonRequest request = iterator.next();

            if (request.getToFloor() == currentFloor) {
                passengers.remove(passengers.indexOf(request));
                TimableOutput.println(
                        "OUT-" + request.getPersonId() + "-" + currentFloor);
            }
        }
    }

    private void move() {
        if (this.status == Status.WAIT) {
            return;
        }
        // 注意，当楼层跨越0时，要多跨一层
        try {
            if (this.status == Status.UP) {
                sleep(udMoveTime);
                this.currentFloor++;
                if (this.currentFloor == 0) {
                    this.currentFloor++;
                }
            } else if (this.status == Status.DOWN) {
                sleep(udMoveTime);
                this.currentFloor--;
                if (this.currentFloor == 0) {
                    this.currentFloor--;
                }
            } else {
                // it won't get here theoretically
                TimableOutput.println("ElevatorStatusException");
            }

            TimableOutput.println("ARRIVE-" + this.currentFloor);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

    }

}
