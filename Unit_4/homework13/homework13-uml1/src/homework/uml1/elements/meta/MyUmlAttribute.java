package homework.uml1.elements.meta;

import com.oocourse.uml1.models.common.NameableType;
import com.oocourse.uml1.models.common.Visibility;
import com.oocourse.uml1.models.elements.UmlAttribute;
import homework.uml1.elements.MyUmlElement;

public class MyUmlAttribute extends MyUmlElement {
    private UmlAttribute umlAttribute;

    public MyUmlAttribute() {}

    public MyUmlAttribute(UmlAttribute umlAttribute) {
        super(umlAttribute);
        this.umlAttribute = umlAttribute;
    }

    public Visibility getVisibility() {
        return umlAttribute.getVisibility();
    }

    /**
     * 返回属性的数据类型
     * @return
     */
    public NameableType getType() {
        return umlAttribute.getType();
    }
}
