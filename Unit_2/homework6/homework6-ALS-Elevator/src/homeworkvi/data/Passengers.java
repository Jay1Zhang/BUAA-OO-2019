package homeworkvi.data;

import com.oocourse.elevator2.PersonRequest;

import java.util.ArrayList;

public class Passengers {
    private final ArrayList<PersonRequest> passengers;

    public Passengers() {
        passengers = new ArrayList<PersonRequest>();
    }

    public int size() {
        return passengers.size();
    }

    public int indexOf(PersonRequest request) {
        return passengers.indexOf(request);
    }

    public boolean isEmpty() {
        return passengers.isEmpty();
    }

    public void putRequest(PersonRequest request) {
        passengers.add(request);
    }

    public PersonRequest getRequest(int index) {
        return passengers.get(index);
    }

    public void remove(int index) {
        passengers.remove(index);
    }

    public boolean hasPassenger(int currentFloor) {
        for (int i = 0; i < passengers.size(); i++) {
            PersonRequest passenger = passengers.get(i);

            if (passenger.getToFloor() == currentFloor) {
                return true;
            }
        }
        return false;
    }

    public ArrayList<PersonRequest> clone() {
        return (ArrayList<PersonRequest>) passengers.clone();
    }
}
