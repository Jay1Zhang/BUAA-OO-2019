package homework.uml2.elements.meta;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlAssociationEnd;
import homework.uml2.elements.MyUmlElement;

public class MyUmlAssociationEnd extends MyUmlElement {
    private UmlAssociationEnd umlAssociationEnd;
    private String clsfrName;
    private ElementType umlType; // class or interface

    public MyUmlAssociationEnd() {}

    public MyUmlAssociationEnd(UmlAssociationEnd umlAssociationEnd) {
        super(umlAssociationEnd);
        this.umlAssociationEnd = umlAssociationEnd;
        this.clsfrName = null;
        this.umlType = null;
    }

    public void setName(String clsfrName) {
        this.clsfrName = clsfrName;
    }

    /* UmlClass or UmlInterface */
    public void setUmlType(ElementType umlType) {
        this.umlType = umlType;
    }

    public String getClsfrName() {
        return clsfrName;
    }

    public ElementType getUmlType() {
        return umlType;
    }

    public String getReference() {
        return umlAssociationEnd.getReference();
    }

    public String getMultiplicity() {
        return umlAssociationEnd.getMultiplicity();
    }

    public Visibility getVisibility() {
        return umlAssociationEnd.getVisibility();
    }
}
