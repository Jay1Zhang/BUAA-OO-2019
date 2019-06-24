package homeworkv.thread;

import homeworkv.data.RequestQueue;

public class Dispatcher extends Thread {
    private final RequestQueue requestQueue = new RequestQueue();
    private final RequestInputDevice requestInputDevice;
    private final Elevator elevator;

    public Dispatcher() {
        requestInputDevice = new RequestInputDevice(requestQueue);
        elevator = new Elevator(requestQueue);
    }

    public void run() {
        requestInputDevice.start();
        elevator.start();
        try {
            while (true) {
                Thread.sleep(1000);
            }
        } catch (InterruptedException e) {
            // print something
            e.printStackTrace();
        }
    }
}
