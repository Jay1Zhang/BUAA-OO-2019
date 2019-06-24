package homeworkvi;

import homeworkvi.data.RequestQueue;
import homeworkvi.thread.Elevator;
import homeworkvi.thread.RequestInputDevice;

public class Main {
    public static void main(String[] args) {
        RequestQueue requestQueue = new RequestQueue();
        new RequestInputDevice(requestQueue).start();
        new Elevator(requestQueue).start();

    }
}
