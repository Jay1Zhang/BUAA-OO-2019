package homework.uml1;

import com.oocourse.uml1.interact.AppRunner;
import homework.uml1.utils.MyUmlInteraction;

public class Main {
    public static void main(String[] args) throws Exception {
        AppRunner appRunner = AppRunner.newInstance(MyUmlInteraction.class);
        appRunner.run(args);
    }
}