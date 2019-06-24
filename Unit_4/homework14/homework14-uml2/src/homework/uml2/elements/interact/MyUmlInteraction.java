package homework.uml2.elements.interact;

import com.oocourse.uml2.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNotFoundException;
import com.oocourse.uml2.models.elements.UmlInteraction;
import com.oocourse.uml2.models.elements.UmlLifeline;
import com.oocourse.uml2.models.elements.UmlMessage;
import homework.uml2.elements.MyUmlElement;
import homework.uml2.elements.meta.MyUmlLifeline;
import homework.uml2.elements.meta.MyUmlMessage;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class MyUmlInteraction extends MyUmlElement {
    // private UmlInteraction umlInteraction;
    private HashSet<MyUmlMessage> messages;
    private HashMap<String, MyUmlLifeline> id2Lifeline;
    private HashMap<String, ArrayList<MyUmlLifeline>> name2Lifeline;

    public MyUmlInteraction() {}

    public MyUmlInteraction(UmlInteraction umlInteraction) {
        super(umlInteraction);
        this.messages = new HashSet<>();
        this.id2Lifeline = new HashMap<>();
        this.name2Lifeline = new HashMap<>();
    }

    public void addMessage(UmlMessage umlMessage) {
        MyUmlMessage myUmlMessage = new MyUmlMessage(umlMessage);
        messages.add(myUmlMessage);

        MyUmlLifeline target = id2Lifeline.get(myUmlMessage.getTargetId());
        if (target == null) {
            return;
        }
        target.setIncomingMessage(myUmlMessage);
    }

    public void addLifeline(UmlLifeline umlLifeline) {
        MyUmlLifeline myUmlLifeline = new MyUmlLifeline(umlLifeline);
        String id = umlLifeline.getId();
        String name = umlLifeline.getName();
        id2Lifeline.put(id, myUmlLifeline);

        ArrayList<MyUmlLifeline> temp;
        if (name2Lifeline.containsKey(name)) {
            temp = name2Lifeline.get(name);
        } else {
            temp = new ArrayList<>();
        }
        temp.add(myUmlLifeline);
        name2Lifeline.put(name, temp);
    }

    public int getParticipantCount() {
        return id2Lifeline.size();
    }

    public int getMessageCount() {
        return messages.size();
    }

    private void checkLifelineName(String interactionName, String lifelineName)
            throws LifelineNotFoundException, LifelineDuplicatedException {
        if (!name2Lifeline.containsKey(lifelineName)) {
            throw new LifelineNotFoundException(interactionName, lifelineName);
        }
        if (name2Lifeline.get(lifelineName).size() > 1) {
            throw new LifelineDuplicatedException(
                    interactionName, lifelineName);
        }
    }

    public int getIncomingMessageCount(
            String interactionName, String lifelineName)
            throws LifelineNotFoundException, LifelineDuplicatedException {
        checkLifelineName(interactionName, lifelineName);

        MyUmlLifeline myUmlLifeline = name2Lifeline.get(lifelineName).get(0);
        return myUmlLifeline.getIncomingMessageCount();
    }
}
