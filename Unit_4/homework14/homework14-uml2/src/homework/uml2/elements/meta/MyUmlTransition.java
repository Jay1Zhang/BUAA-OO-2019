package homework.uml2.elements.meta;

import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlTransition;
import homework.uml2.elements.MyUmlElement;

public class MyUmlTransition extends MyUmlElement {
    private UmlTransition umlTransition;

    public MyUmlTransition() {}

    public MyUmlTransition(UmlTransition umlTransition) {
        super(umlTransition);
        this.umlTransition = umlTransition;
    }

    public String getSourceId() {
        return umlTransition.getSource();
    }

    public String getTargetId() {
        return umlTransition.getTarget();
    }

    public String getGuard() {
        return umlTransition.getGuard();
    }

    public Visibility getVisibility() {
        return umlTransition.getVisibility();
    }
}
