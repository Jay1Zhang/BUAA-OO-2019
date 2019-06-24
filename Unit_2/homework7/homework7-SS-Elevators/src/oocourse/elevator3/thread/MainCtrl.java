package oocourse.elevator3.thread;

import oocourse.elevator3.data.Request;
import oocourse.elevator3.data.RequestQueue;
import oocourse.elevator3.data.WaitingQueue;

import java.util.ArrayList;

import static oocourse.elevator3.data.Config.dockableFloorsOfA;
import static oocourse.elevator3.data.Config.moveTimeOfA;
import static oocourse.elevator3.data.Config.maxNumOfA;
import static oocourse.elevator3.data.Config.dockableFloorsOfB;
import static oocourse.elevator3.data.Config.moveTimeOfB;
import static oocourse.elevator3.data.Config.maxNumOfB;
import static oocourse.elevator3.data.Config.dockableFloorsOfC;
import static oocourse.elevator3.data.Config.moveTimeOfC;
import static oocourse.elevator3.data.Config.maxNumOfC;
import static oocourse.elevator3.data.Config.ocDoorTime;
import static oocourse.elevator3.data.Config.EleId;
import static oocourse.elevator3.data.Config.Status;

public class MainCtrl extends Thread {
    private final RequestQueue requestQueue;
    private final WaitingQueue waitingQueueA;
    private final WaitingQueue waitingQueueB;
    private final WaitingQueue waitingQueueC;
    private final Elevator elevatorA;
    private final Elevator elevatorB;
    private final Elevator elevatorC;

    public MainCtrl(RequestQueue requestQueue) {
        super("Thread-MainCtrl");
        this.requestQueue = requestQueue;
        this.waitingQueueA = new WaitingQueue();
        this.waitingQueueB = new WaitingQueue();
        this.waitingQueueC = new WaitingQueue();

        this.elevatorA = new Elevator("A",
                dockableFloorsOfA, moveTimeOfA, ocDoorTime, maxNumOfA,
                requestQueue, waitingQueueA);
        this.elevatorB = new Elevator("B",
                dockableFloorsOfB, moveTimeOfB, ocDoorTime, maxNumOfB,
                requestQueue, waitingQueueB);
        this.elevatorC = new Elevator("C",
                dockableFloorsOfC, moveTimeOfC, ocDoorTime, maxNumOfC,
                requestQueue, waitingQueueC);
    }

    @Override
    public void run() {
        this.elevatorA.start();
        this.elevatorB.start();
        this.elevatorC.start();

        while (true) {
            // 0. 检查线程是否可以停止
            if (requestQueue.InputEnd() && requestQueue.isEmpty() &&
                    elevatorA.isStill() && elevatorB.isStill() &&
                    elevatorC.isStill()) {
                waitingQueueA.setMainCtrlEndTag(true);
                //waitingQueueB.setMainCtrlEndTag(true);
                //waitingQueueC.setMainCtrlEndTag(true);
                break;
            }

            // 1. 从请求队列中拿出请求
            Request request = requestQueue.getRequest();
            // 若get到null,说明输入线程结束且请求队列为空
            if (request == null) {
                continue;
            }

            // 2. 根据一定调度规则，将该请求加入电梯的停靠队列中
            dispatchRequest(request);
        }
        //TimableOutput.println(currentThread().getName() + " done.");
    }

    private void dispatchRequest(Request request) {
        ArrayList<EleId> optEleList = request.getOptEleList();
        // 优先选择空闲电梯, 且从A开始
        for (int i = 0; i < optEleList.size(); i++) {
            EleId eleId = optEleList.get(i);

            switch (eleId) {
                case A:
                    if (elevatorA.getStatus() == Status.WAIT) {
                        waitingQueueA.putRequest(request);
                        return;
                    }
                    break;
                case B:
                    if (elevatorB.getStatus() == Status.WAIT) {
                        waitingQueueB.putRequest(request);
                        return;
                    }
                    break;
                case C:
                    if (elevatorC.getStatus() == Status.WAIT) {
                        waitingQueueC.putRequest(request);
                        return;
                    }
                    break;
                default:
                        // do nothing
            }
        }

        // 若三部电梯均忙碌，则选择人未满的上
        for (int i = 0; i < optEleList.size(); i++) {
            EleId eleId = optEleList.get(i);

            switch (eleId) {
                case A:
                    if (!elevatorA.isFull()) {
                        waitingQueueA.putRequest(request);
                        return;
                    }
                    break;
                case B:
                    if (!elevatorB.isFull()) {
                        waitingQueueB.putRequest(request);
                        return;
                    }
                    break;
                case C:
                    if (!elevatorC.isFull()) {
                        waitingQueueC.putRequest(request);
                        return;
                    }
                    break;
                default:
                    // do nothing
            }
        }

        // 若三部电梯都满了
        //  不好意思, 早高峰, 能挤上哪个上哪个吧
        if (request.contains(EleId.A)) {
            waitingQueueA.putRequest(request);
        } else if (request.contains(EleId.B)) {
            waitingQueueB.putRequest(request);
        } else {
            waitingQueueC.putRequest(request);
        }
    }
}
