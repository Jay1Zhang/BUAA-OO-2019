package homeworkvi.data;

public class Constant {
    public enum Status {
        ARRIVE, OPEN, CLOSE, WAIT, UP, DOWN;
    }

    public static final long osDoorTime = 400; // time to open & close the door
    public static final long udMoveTime = 400; // time to up or down one level
    public static final long openTime = 350;
    public static final long closeTime = 50;
}
