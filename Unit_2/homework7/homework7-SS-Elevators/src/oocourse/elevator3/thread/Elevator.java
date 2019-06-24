package oocourse.elevator3.thread;

import com.oocourse.TimableOutput;
import oocourse.elevator3.data.Dispatcher;
import oocourse.elevator3.data.Config.Status;
import oocourse.elevator3.data.Passengers;
import oocourse.elevator3.data.Request;
import oocourse.elevator3.data.RequestQueue;
import oocourse.elevator3.data.WaitingQueue;

import java.util.ArrayList;

public class Elevator extends Thread {
    // fixed attribute
    private final String name;
    private final ArrayList<Integer> dockableFloors;
    private final long moveTime;
    private final long ocDoorTime;
    private final int maxNum;
    // static attribute
    private final RequestQueue requestQueue;
    private final WaitingQueue waitingQueue;
    private final Passengers passengers;
    private final Dispatcher dispatcher;
    // dynamic attribute
    private int currentFloor = 1;
    private int numOfPsgers = 0;
    private Status status = Status.WAIT;

    public Elevator(String name, ArrayList<Integer> dockableFloors,
                    long moveTime, long ocDoorTime, int maxNum,
                    RequestQueue requestQueue, WaitingQueue waitingQueue)
    {
        this.name = name;
        this.dockableFloors = dockableFloors;
        this.moveTime = moveTime;
        this.ocDoorTime = ocDoorTime;
        this.maxNum = maxNum;
        this.requestQueue = requestQueue;
        this.waitingQueue = waitingQueue;
        this.passengers = new Passengers();
        this.dispatcher = new Dispatcher(waitingQueue, this);
    }

    @Override
    public void run() {
        try {
            while (true) {
                // 0. check if it's over
                // 若电梯处于WAIT状态且等待队列为空, break
                if (isStill() && waitingQueue.isMainCtrlEndTag()) {
                    break;
                }

                // 1. take or send passengers if there is a need
                if ((waitingQueue.hasWaitRqst(currentFloor, status, isEmpty())
                        && !isFull())
                        || passengers.hasPassenger(currentFloor)) {
                    // 1.1 open the door
                    TimableOutput.println("OPEN-" + currentFloor + "-" + name);
                    sleep(ocDoorTime);

                    // 1.2 pick up sb.
                    sendPassengers();
                    takePassengers();
                    // 1.3 drop off sb.

                    // 1.4 close the door
                    TimableOutput.println("CLOSE-" + currentFloor + "-" + name);
                }
                // 2. update the elevator status
                updateStatus();
                // 3. move
                move();

            }
            //TimableOutput.println("Thread-Elevator" + name + " done.");
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public boolean isFull() {
        if (passengers.size() == maxNum) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isEmpty() {
        return passengers.isEmpty();
    }

    public boolean isStill() {
        if (status == Status.WAIT && waitingQueue.isEmpty()
                && passengers.isEmpty()) {
            return true;
        } else {
            return false;
        }
    }

    public int getCurrentFloor() {
        return currentFloor;
    }

    public Status getStatus() {
        return status;
    }

    public int getNumOfPsgers() {
        return numOfPsgers;
    }

    private void takePassengers() {
        // 若等待队列中有当前楼层的请求 且 电梯未满 - IN
        while (waitingQueue.hasWaitRqst(currentFloor, status, isEmpty())
                && !isFull()) {
            Request waitRqst = waitingQueue.nextWaitRqst(
                    currentFloor, status, isEmpty());

            passengers.putRequest(waitRqst);
            TimableOutput.println("IN-" +
                    waitRqst.getPersonId() + "-" + currentFloor + "-" + name);
            updateStatus(); // 保证实时更新电梯的状态
        }
    }

    private void sendPassengers() {
        // 若乘客队列中有当前楼层的请求 - OUT
        while (passengers.hasPassenger(currentFloor)) {
            Request passenger = passengers.nextPassenger(currentFloor);

            TimableOutput.println("OUT-" +
                    passenger.getPersonId() + "-" + currentFloor + "-" + name);
            // 该请求完成, 判断是否有子请求
            if (passenger.hasChildRqst()) {
                // 更换主请求, 使得子请求对外可见, 并重新放入请求队列
                passenger.changeMainRqst();
                requestQueue.putRequest(passenger);
                //TimableOutput.println("Test: "+ passenger +
                // " rqstQueue isEmpty? " + requestQueue.isEmpty());
            }

            updateStatus(); // 保证实时更新电梯的状态
        }
    }

    private void updateStatus() {
        // 如果电梯中有乘客，根据到达时间最早乘客的需求送人
        if (!passengers.isEmpty()) {
            Request request = passengers.getFirstRequest();
            //TimableOutput.println(
            // "Elevator" + name + " get request from passengers: " + request);
            this.status = request.getStatus();
            return;
        }
        // 如果电梯为空, 而等待队列有乘客，则去接人
        if (!waitingQueue.isEmpty()) {
            Request request = waitingQueue.getFirstRequest();
            //TimableOutput.println(
            // "Elevator" + name + " get request from waitingQueue: " +request);
            if (currentFloor < request.getFromFloor()) {
                this.status = Status.UP;
            } else if (currentFloor > request.getFromFloor()) {
                this.status = Status.DOWN;
            } else {
                // it won't get here theoretically
                // 若电梯为空,且等待队列的当前层有请求, 必然已经接上来了
            }

            return;
        }
        // if there is nothing to do, WAIT
        this.status = Status.WAIT;
    }

    private void move() {
        // 注意，当楼层跨越0时，要多跨一层
        try {
            if (this.status == Status.WAIT) {
                sleep(5);
                requestQueue.doNotify();
                return;

            } else if (this.status == Status.UP) {
                sleep(moveTime);
                this.currentFloor++;
                if (this.currentFloor == 0) {
                    this.currentFloor++;
                }
            } else if (this.status == Status.DOWN) {
                sleep(moveTime);
                this.currentFloor--;
                if (this.currentFloor == 0) {
                    this.currentFloor--;
                }
            } else {
                // it won't get here theoretically
                TimableOutput.println("ElevatorStatusException");
            }

            TimableOutput.println("ARRIVE-" + this.currentFloor + "-" + name);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

    }
}
