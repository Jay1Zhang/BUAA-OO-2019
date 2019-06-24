package homework.uml2.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.elements.UmlElement;

public abstract class MyUmlElement {
    private UmlElement umlElement;

    public MyUmlElement() {}

    public MyUmlElement(UmlElement umlElement) {
        this.umlElement = umlElement;
    }

    public UmlElement getSelf() {
        return umlElement;
    }

    public String getName() {
        return umlElement.getName();
    }

    public String getId() {
        return umlElement.getId();
    }

    public String getParentId() {
        return umlElement.getParentId();
    }

    public ElementType getElementType() {
        return umlElement.getElementType();
    }

    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }

        if (obj == null || this.getClass() != obj.getClass()) {
            return false;
        }

        MyUmlElement that = (MyUmlElement) obj;
        return umlElement.equals(that.getSelf());
    }

    public int hashCode() {
        return umlElement.hashCode();
    }
}
