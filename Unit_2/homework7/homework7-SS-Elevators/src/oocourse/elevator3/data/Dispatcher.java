package oocourse.elevator3.data;

import oocourse.elevator3.thread.Elevator;

public class Dispatcher {
    private final WaitingQueue waitingQueue;
    private final Elevator elevator;

    public Dispatcher(WaitingQueue waitingQueue, Elevator elevator) {
        this.waitingQueue = waitingQueue;
        this.elevator = elevator;
    }

}
