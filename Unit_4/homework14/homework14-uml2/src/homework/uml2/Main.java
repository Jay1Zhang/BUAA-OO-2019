package homework.uml2;

import com.oocourse.uml2.interact.AppRunner;
import homework.uml2.utils.MyUmlGeneralInteraction;

public class Main {
    public static void main(String[] args) throws Exception {
        AppRunner appRunner =
                AppRunner.newInstance(MyUmlGeneralInteraction.class);
        appRunner.run(args);
    }
}