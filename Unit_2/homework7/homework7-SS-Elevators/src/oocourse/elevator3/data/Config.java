package oocourse.elevator3.data;

import java.util.ArrayList;
import java.util.Arrays;

public abstract class Config {

    public static final ArrayList<Integer> dockableFloorsOfA =
            new ArrayList<Integer>(
                    Arrays.asList(-3, -2, -1, 1, 15, 16, 17, 18, 19, 20));
    public static final ArrayList<Integer> dockableFloorsOfB =
            new ArrayList<Integer>(
                    Arrays.asList(-2, -1, 1, 2, 4, 5, 6, 7, 8, 9, 10,
                            11, 12, 13, 14, 15));
    public static final ArrayList<Integer> dockableFloorsOfC =
            new ArrayList<Integer>(
                    Arrays.asList(1, 3, 5, 7, 9, 11, 13, 15)
            );

    public static final long moveTimeOfA = 400;
    public static final long moveTimeOfB = 500;
    public static final long moveTimeOfC = 600;

    public static final long openTime = 200;
    public static final long closeTime = 200;
    public static final long ocDoorTime = openTime + closeTime;

    public static final int maxNumOfA = 6;
    public static final int maxNumOfB = 8;
    public static final int maxNumOfC = 7;

    public static final int initNum = 0;

    public enum Status {
        ARRIVE, OPEN, CLOSE, WAIT, UP, DOWN;
    }

    public enum EleId {
        A, B, C;
    }
}
