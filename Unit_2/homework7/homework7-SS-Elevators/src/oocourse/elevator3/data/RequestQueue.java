package oocourse.elevator3.data;

import java.util.LinkedList;
import java.util.Queue;

public class RequestQueue {
    private final Queue<Request> queue = new LinkedList<Request>();
    private volatile boolean inputEndTag = false; // input end tag

    public void setInputEndTag(boolean endTag) {
        this.inputEndTag = endTag;
    }

    public boolean InputEnd() {
        return inputEndTag;
    }

    public synchronized boolean isEmpty() {
        return queue.isEmpty();
    }

    public synchronized Request getRequest() {
        while (queue.peek() == null) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
            // 主控器被唤醒的原因可能有两个
            //      1. putRequest, 输入了新请求, 直接返回队首请求
            //      2. 被电梯叫醒
            //  因而，需要检查输入线程是否结束且队列是否为空，防止死锁
            if (InputEnd() && isEmpty()) {
                return null;
            }

        }
        return queue.remove();
    }

    public synchronized void putRequest(Request request) {
        queue.offer(request);
        notifyAll();
    }

    public synchronized void doNotify() {
        notifyAll();
    }
}
