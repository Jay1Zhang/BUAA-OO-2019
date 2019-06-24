package homework.uml2.elements.state;

import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlPseudostate;
import homework.uml2.elements.MyUmlElement;

import java.util.HashSet;

public class MyUmlPseudostate extends MyUmlElement {
    private UmlPseudostate umlPseudostate;
    private HashSet<MyUmlState> nextStateSet;
    private HashSet<MyUmlFinalState> finalStateSet;

    public MyUmlPseudostate() {}

    public MyUmlPseudostate(UmlPseudostate umlPseudostate) {
        super(umlPseudostate);
        this.umlPseudostate = umlPseudostate;
        this.nextStateSet = new HashSet<>();
        this.finalStateSet = new HashSet<>();
    }

    public Visibility getVisibility() {
        return umlPseudostate.getVisibility();
    }

    public void setNextState(MyUmlState myUmlState) {
        nextStateSet.add(myUmlState);
    }

    public void setFinalState(MyUmlFinalState myUmlFinalState) {
        finalStateSet.add(myUmlFinalState);
    }
}
