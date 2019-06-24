package homework.uml2.elements.meta;

import com.oocourse.uml2.models.common.Direction;
import com.oocourse.uml2.models.common.NameableType;
import com.oocourse.uml2.models.elements.UmlParameter;
import homework.uml2.elements.MyUmlElement;

public class MyUmlParameter extends MyUmlElement {
    private UmlParameter umlParameter;

    public MyUmlParameter() {}

    public MyUmlParameter(UmlParameter umlParameter) {
        super(umlParameter);
        this.umlParameter = umlParameter;
    }

    public Direction getDirection() {
        return umlParameter.getDirection();
    }

    /**
     * 返回参数的数据类型
     * @return
     */
    public NameableType getType() {
        return umlParameter.getType();
    }
}
