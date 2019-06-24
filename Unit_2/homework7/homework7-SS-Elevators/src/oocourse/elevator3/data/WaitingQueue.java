package oocourse.elevator3.data;

import java.util.ArrayList;

import oocourse.elevator3.data.Config.Status;

public class WaitingQueue {
    private final ArrayList<Request> queue = new ArrayList<Request>();
    private static volatile boolean mainCtrlEndTag = false;

    public static void setMainCtrlEndTag(boolean bool) {
        mainCtrlEndTag = bool;
    }

    public static boolean isMainCtrlEndTag() {
        return mainCtrlEndTag;
    }

    public synchronized boolean isEmpty() {
        return queue.isEmpty();
    }

    public synchronized int size() {
        return queue.size();
    }

    public synchronized void putRequest(Request request) {
        queue.add(request);
    }

    public synchronized Request getRequest(int index) {
        return queue.get(index);
    }

    public synchronized Request getFirstRequest() {
        return getRequest(0);
    }

    public synchronized void remove(int index) {
        queue.remove(index);
    }

    /**
     * 顾名思义，判断当前楼层是否有需要接的人
     * 根据电梯的当前状态判断是否需要在当前层停下并接人
     * @param currentFloor
     * @param status
     * @return
     */
    public boolean hasWaitRqst(int currentFloor, Status status,
                               boolean isEmpty) {
        for (int i = 0; i < size(); i++) {
            Request request = queue.get(i);

            if (request.getFromFloor() == currentFloor) {
                // 1. 电梯WAIT中
                // 2. 电梯为空, 可能要去接人
                // 3. 电梯运行方向与该请求方向一致, 捎带
                if ((status == Status.WAIT) || isEmpty
                        || (request.getStatus() == status)) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * 与 getRequest() 的很大区别在于：
     * 该方法会将get到的请求从waitingQueue中移除
     * @param currentFloor
     * @param status
     * @return
     */
    public Request nextWaitRqst(int currentFloor, Status status,
                                boolean isEmpty) {
        for (int i = 0; i < queue.size(); i++) {
            Request request = queue.get(i);

            if (request.getFromFloor() == currentFloor) {
                // 1. 电梯WAIT中
                // 2. 电梯为空, 可能要去接人
                // 3. 电梯运行方向与该请求方向一致, 捎带
                if ((status == Status.WAIT) || isEmpty
                        || (request.getStatus() == status)) {
                    queue.remove(i);
                    return request;
                }
            }
            // 注意
            // 当电梯处于WAIT状态且该层楼有多个请求时，会把这些人都带上来...
            // 虽然不符合实际，乘客可能会又上又下的
            // 但性能上好像并不影响，甚至会更好...
            // 毕竟你总要上电梯的，跟别人一起上的话电梯岂不是少在你这层楼停一次了？
        }
        return null;
    }

}
