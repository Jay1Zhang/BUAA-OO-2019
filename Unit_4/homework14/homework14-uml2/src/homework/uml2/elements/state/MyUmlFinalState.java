package homework.uml2.elements.state;

import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlFinalState;
import homework.uml2.elements.MyUmlElement;

public class MyUmlFinalState extends MyUmlElement {
    private UmlFinalState umlFinalState;

    public MyUmlFinalState() {}

    public MyUmlFinalState(UmlFinalState umlFinalState) {
        super(umlFinalState);
        this.umlFinalState = umlFinalState;
    }

    public Visibility getVisibility() {
        return umlFinalState.getVisibility();
    }
}
