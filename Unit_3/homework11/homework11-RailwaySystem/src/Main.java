import com.oocourse.specs3.AppRunner;
import util.MyPath;
import util.MyRailwaySystem;

public class Main {
    public static void main(String[] args) throws Exception {
        long last = System.currentTimeMillis();
        AppRunner runner = AppRunner.newInstance(
                MyPath.class, MyRailwaySystem.class);
        runner.run(args);
        long current = System.currentTimeMillis();
        System.out.println(current - last);
    }
}