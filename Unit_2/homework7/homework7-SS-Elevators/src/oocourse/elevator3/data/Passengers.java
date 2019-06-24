package oocourse.elevator3.data;

import java.util.ArrayList;

public class Passengers {
    private final ArrayList<Request> passengers = new ArrayList<Request>();

    public synchronized int size() {
        return passengers.size();
    }

    public synchronized boolean isEmpty() {
        return passengers.isEmpty();
    }

    public synchronized void putRequest(Request request) {
        this.passengers.add(request);
    }

    public synchronized Request getRequest(int index) {
        return passengers.get(index);
    }

    public synchronized Request getFirstRequest() {
        return getRequest(0);
    }

    public synchronized void remove(int index) {
        passengers.remove(index);
    }

    /**
     * 检查是否有需要在当前层下电梯的乘客
     * 此处判断逻辑相比等待队列要简单的多
     * @param currentFloor
     * @return
     */
    public boolean hasPassenger(int currentFloor) {
        for (int i = 0; i < passengers.size(); i++) {
            Request request = passengers.get(i);

            if (request.getToFloor() == currentFloor) {
                return true;
            }
        }
        return false;
    }

    /**
     * 与 getRequest() 方法的很大区别在于
     * 该方法会将下一个get到的请求从乘客队列移除
     * @param currentFloor
     * @return
     */
    public Request nextPassenger(int currentFloor) {
        for (int i = 0; i < size(); i++) {
            Request request = passengers.get(i);

            if (request.getToFloor() == currentFloor) {
                remove(i);
                return request;
            }
        }
        return null;
    }
}
