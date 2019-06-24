package homework.uml2.elements.classifier;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlInterface;
import homework.uml2.elements.meta.MyUmlAssociationEnd;
import homework.uml2.elements.meta.MyUmlAttribute;
import homework.uml2.elements.MyUmlElement;
import homework.uml2.elements.meta.MyUmlOperation;

import java.util.HashMap;
import java.util.HashSet;

// MyUmlClass or MyUmlInterface -> MyUmlClassifier
public class MyUmlClassifier extends MyUmlElement {
    // attribute 属性不会重名
    private HashMap<String, MyUmlAttribute> name2Attr;
    private HashMap<String, MyUmlAttribute> id2Attr;
    // operation 操作可能重名
    private HashMap<String, HashSet<MyUmlOperation>> name2Opera;
    // association 关联可能重名，但无需通过name访问
    private HashMap<String, MyUmlAssociationEnd> id2Assoc;

    public MyUmlClassifier() {}

    public MyUmlClassifier(UmlElement umlElement) {
        super(umlElement);
        this.name2Attr = new HashMap<>();
        this.id2Attr = new HashMap<>();
        this.name2Opera = new HashMap<>();
        this.id2Assoc = new HashMap<>();
    }

    public void setAttribute(MyUmlAttribute myUmlAttribute) {
        String id = myUmlAttribute.getId();
        String name = myUmlAttribute.getName();
        name2Attr.put(name, myUmlAttribute);
        id2Attr.put(id, myUmlAttribute);
    }

    public void setOperation(MyUmlOperation myUmlOperation) {
        String name = myUmlOperation.getName();

        HashSet<MyUmlOperation> temp;
        if (name2Opera.containsKey(name)) {
            temp = name2Opera.get(name);
        } else {
            temp = new HashSet<>();
        }
        temp.add(myUmlOperation);
        name2Opera.put(name, temp);
    }

    public void setAssociation(MyUmlAssociationEnd myUmlAssociationEnd) {
        String id = myUmlAssociationEnd.getId();
        id2Assoc.put(id, myUmlAssociationEnd);
    }

    public HashMap<String, MyUmlAttribute> getId2Attr() {
        return id2Attr;
    }

    public HashMap<String, MyUmlAttribute> getName2Attr() {
        return name2Attr;
    }

    public HashMap<String, HashSet<MyUmlOperation>> getName2Opera() {
        return name2Opera;
    }

    public HashMap<String, MyUmlAssociationEnd> getId2Assoc() {
        return id2Assoc;
    }

    public Visibility getVisibility() {
        UmlElement umlElement = super.getSelf();
        if (umlElement.getElementType().equals(ElementType.UML_CLASS)) {
            UmlClass umlClass = (UmlClass) umlElement;
            return umlClass.getVisibility();
        } else {
            UmlInterface umlInterface = (UmlInterface) umlElement;
            return umlInterface.getVisibility();
        }
    }
}
