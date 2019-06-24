package homework.uml1.elements.meta;

import com.oocourse.uml1.models.common.ElementType;
import com.oocourse.uml1.models.common.Visibility;
import com.oocourse.uml1.models.elements.UmlAssociationEnd;
import homework.uml1.elements.MyUmlElement;

public class MyUmlAssociationEnd extends MyUmlElement {
    private UmlAssociationEnd umlAssociationEnd;
    private String name;
    private ElementType umlType; // class or interface

    public MyUmlAssociationEnd() {}

    public MyUmlAssociationEnd(UmlAssociationEnd umlAssociationEnd) {
        super(umlAssociationEnd);
        this.umlAssociationEnd = umlAssociationEnd;
        this.name = null;
        this.umlType = null;
    }

    public void setName(String name) {
        this.name = name;
    }

    /* UmlClass or UmlInterface */
    public void setUmlType(ElementType umlType) {
        this.umlType = umlType;
    }

    @Override
    public String getName() {
        return name;
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
