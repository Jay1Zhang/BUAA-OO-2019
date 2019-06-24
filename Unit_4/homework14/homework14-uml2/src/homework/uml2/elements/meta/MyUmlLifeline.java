package homework.uml2.elements.meta;

import com.oocourse.uml2.models.elements.UmlLifeline;
import homework.uml2.elements.MyUmlElement;

import java.util.HashSet;

public class MyUmlLifeline extends MyUmlElement {
    private UmlLifeline umlLifeline;
    private HashSet<MyUmlMessage> incomingMessages;

    public MyUmlLifeline() {}

    public MyUmlLifeline(UmlLifeline umlLifeline) {
        super(umlLifeline);
        this.umlLifeline = umlLifeline;
        this.incomingMessages = new HashSet<>();
    }

    public void setIncomingMessage(MyUmlMessage myUmlMessage) {
        incomingMessages.add(myUmlMessage);
    }

    public boolean isMultiInstance() {
        return umlLifeline.isMultiInstance();
    }

    public String getRoleId() {
        return umlLifeline.getRepresent();
    }

    public int getIncomingMessageCount() {
        return incomingMessages.size();
    }
}
