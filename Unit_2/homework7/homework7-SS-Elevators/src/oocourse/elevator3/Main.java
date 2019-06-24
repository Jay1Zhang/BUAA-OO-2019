package oocourse.elevator3;

import com.oocourse.TimableOutput;
import oocourse.elevator3.data.RequestQueue;
import oocourse.elevator3.thread.MainCtrl;
import oocourse.elevator3.thread.RqstInputDevice;

public class Main {
    public static void main(String[] args) {
        // please MUST initialize start timestamp at the beginning
        TimableOutput.initStartTimestamp();

        RequestQueue requestQueue = new RequestQueue();
        new RqstInputDevice(requestQueue).start();
        new MainCtrl(requestQueue).start();
    }
}
