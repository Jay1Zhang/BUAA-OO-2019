import com.oocourse.TimableOutput;

class SelfTestMainClassForTimableOutput {
    public static void main(String[] args) throws Exception {
        // please MUST initialize start timestamp at the beginning
        TimableOutput.initStartTimestamp();

        // print something
        TimableOutput.println(1.0 / 7);

        // sleep for a while, then print something again
        Thread.sleep(1000);
        TimableOutput.println(
                String.format("result of 2 / 7 is %.10f", 2.0 / 7));

        // sleep for a while, then print something again
        Thread.sleep(3000);
        TimableOutput.println(
                String.format("result of 3 / 7 is %.10f", 3.0 / 7));
    }
}