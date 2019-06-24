package homework.uml2.elements.meta;

import com.oocourse.uml2.models.common.MessageSort;
import com.oocourse.uml2.models.elements.UmlMessage;
import homework.uml2.elements.MyUmlElement;

public class MyUmlMessage extends MyUmlElement {
    private UmlMessage umlMessage;

    public MyUmlMessage() {}

    public MyUmlMessage(UmlMessage umlMessage) {
        super(umlMessage);
        this.umlMessage = umlMessage;
    }

    public MessageSort getMessageSort() {
        return umlMessage.getMessageSort();
    }

    public String getSourceId() {
        return umlMessage.getSource();
    }

    public String getTargetId() {
        return umlMessage.getTarget();
    }
}
