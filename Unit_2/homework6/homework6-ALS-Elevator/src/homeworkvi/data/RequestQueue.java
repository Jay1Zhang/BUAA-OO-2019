package homeworkvi.data;

import com.oocourse.elevator2.PersonRequest;

import java.util.ArrayList;

public class RequestQueue {
    private final ArrayList<PersonRequest> queue =
            new ArrayList<PersonRequest>();
    private volatile boolean endTag = false; // input end tag

    public synchronized void setEndTag(boolean flag) {
        this.endTag = flag;
        notifyAll();
    }

    public boolean InputEnd() {
        if (queue.isEmpty() && endTag) {
            return true;
        } else {
            return false;
        }
    }

    public int indexOf(PersonRequest request) {
        return queue.indexOf(request);
    }

    public int size() {
        return queue.size();
    }

    public void remove(int index) {
        queue.remove(index);
    }

    /**
     * 用于请求输入装置与调度器的交互
     * 注意是返回队首元素，且remove掉
     * @return
     */
    public synchronized PersonRequest getRequest() {
        while (queue.isEmpty()) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
            if (InputEnd()) {
                return null;
            }
        }
        return queue.remove(0);
    }

    /**
     * 用于遍历队列元素
     * @param index
     * @return
     */
    public synchronized PersonRequest getRequest(int index) {
        return queue.get(index);
    }

    public synchronized void putRequest(PersonRequest personRequest) {
        queue.add(personRequest);
        notifyAll();
    }

    public ArrayList<PersonRequest> clone() {
        return (ArrayList<PersonRequest>) queue.clone();
    }
}
