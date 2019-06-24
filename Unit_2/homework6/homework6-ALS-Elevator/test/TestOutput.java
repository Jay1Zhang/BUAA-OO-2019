import com.oocourse.TimableOutput;

public class TestOutput {
    public static void main(String[] args) throws Exception {
        TimableOutput.initStartTimestamp();
        TimableOutput.println(0.14285714285714285D);
        TimableOutput.println(0.14285714285714285D);
        TimableOutput.println(0.14285714285714285D);
        TimableOutput.println(0.14285714285714285D);
        TimableOutput.println(0.14285714285714285D);
        Thread.sleep(1000L);
        TimableOutput.println(String.format("result of 2 / 7 is %.10f", 0.2857142857142857D));
        Thread.sleep(3000L);
        TimableOutput.println(String.format("result of 3 / 7 is %.10f", 0.42857142857142855D));
    }
}
