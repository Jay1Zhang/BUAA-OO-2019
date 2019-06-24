package homework.uml2.elements.meta;

import com.oocourse.uml2.models.common.Direction;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlOperation;
import homework.uml2.elements.MyUmlElement;

import java.util.HashSet;

public class MyUmlOperation extends MyUmlElement {
    private UmlOperation umlOperation;
    private HashSet<MyUmlParameter> parameterSet;
    private MyUmlParameter returnType;

    public MyUmlOperation() {}

    public MyUmlOperation(UmlOperation umlOperation) {
        super(umlOperation);
        this.umlOperation = umlOperation;
        this.parameterSet = new HashSet<>();
        this.returnType = null;
    }

    public boolean hasPara() {
        if (parameterSet.isEmpty()) {
            return false;
        } else {
            return true;
        }
    }

    public boolean hasReturn() {
        if (returnType == null) {
            return false;
        } else {
            return true;
        }
    }

    /**
     * 根据参数类型设置参数
     * @param myUmlParameter
     */
    public void setPara(MyUmlParameter myUmlParameter) {
        if (myUmlParameter.getDirection().equals(Direction.IN)) {
            parameterSet.add(myUmlParameter);
        } else if (myUmlParameter.getDirection().equals(Direction.RETURN)) {
            returnType = myUmlParameter;
        }
    }

    public Visibility getVisibility() {
        return umlOperation.getVisibility();
    }
}
