package homeworkvi.data;

import com.oocourse.elevator2.PersonRequest;

import java.util.ArrayList;

public class PiggybackQueue {
    private final ArrayList<PersonRequest> queue =
            new ArrayList<PersonRequest>();
    private volatile boolean dispatchEndTag = false;
    private volatile boolean flag = true;

    public boolean getFlag() {
        return flag;
    }

    public synchronized void setFlag(boolean bool) {
        flag = bool;
    }

    public void setDispatchEndTag(boolean flag) {
        this.dispatchEndTag = flag;
    }

    public boolean dispatchEnd() {
        return this.dispatchEndTag;
    }

    public int size() {
        return queue.size();
    }

    public int indexOf(PersonRequest request) {
        return queue.indexOf(request);
    }

    public boolean isEmpty() {
        return queue.isEmpty();
    }

    public synchronized void putRequest(PersonRequest personRequest) {
        queue.add(personRequest);
    }

    public synchronized PersonRequest getRequest(int index) {
        return queue.get(index);
    }

    public synchronized void remove(int index) {
        queue.remove(index);
    }

    public boolean hasPiggyback(int currentFloor) {
        for (int i = 0; i < queue.size(); i++) {
            PersonRequest request = queue.get(i);

            if (request.getFromFloor() == currentFloor) {
                return true;
            }
        }
        return false;
    }

    public ArrayList<PersonRequest> clone() {
        return (ArrayList<PersonRequest>) queue.clone();
    }
}
