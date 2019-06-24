package homework.uml2.utils;

import com.oocourse.uml2.interact.exceptions.user.InteractionDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.InteractionNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNotFoundException;
import com.oocourse.uml2.interact.format.UmlCollaborationInteraction;
import com.oocourse.uml2.models.elements.UmlAttribute;
import com.oocourse.uml2.models.elements.UmlInteraction;
import com.oocourse.uml2.models.elements.UmlLifeline;
import com.oocourse.uml2.models.elements.UmlMessage;
import homework.uml2.elements.interact.MyUmlInteraction;
import homework.uml2.elements.meta.MyUmlAttribute;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

/**
 * UML顺序图交互
 */
public class MyUmlCollaborationInteraction
        implements UmlCollaborationInteraction {
    private HashSet<MyUmlAttribute> roles;
    private HashMap<String, MyUmlInteraction> id2Interaction;
    private HashMap<String, ArrayList<MyUmlInteraction>> name2Interaction;

    public MyUmlCollaborationInteraction() {
        this.roles = new HashSet<>();
        this.id2Interaction = new HashMap<>();
        this.name2Interaction = new HashMap<>();
    }

    public void addRole(UmlAttribute umlAttribute) {
        MyUmlAttribute myUmlAttribute = new MyUmlAttribute(umlAttribute);
        roles.add(myUmlAttribute);
    }

    public void addInteraction(UmlInteraction umlInteraction) {
        MyUmlInteraction myUmlInteraction =
                new MyUmlInteraction(umlInteraction);
        String id = umlInteraction.getId();
        String name = umlInteraction.getName();
        id2Interaction.put(id, myUmlInteraction);

        ArrayList<MyUmlInteraction> temp;
        if (name2Interaction.containsKey(name)) {
            temp = name2Interaction.get(name);
        } else {
            temp = new ArrayList<>();
        }
        temp.add(myUmlInteraction);
        name2Interaction.put(name, temp);
    }

    public void addMessage(UmlMessage umlMessage) {
        MyUmlInteraction myUmlInteraction =
                id2Interaction.get(umlMessage.getParentId());
        myUmlInteraction.addMessage(umlMessage);
    }

    public void addLifeline(UmlLifeline umlLifeline) {
        MyUmlInteraction myUmlInteraction =
                id2Interaction.get(umlLifeline.getParentId());
        myUmlInteraction.addLifeline(umlLifeline);
    }

    private void checkInteractionName(String interactionName) throws
            InteractionNotFoundException, InteractionDuplicatedException {
        if (!name2Interaction.containsKey(interactionName)) {
            throw new InteractionNotFoundException(interactionName);
        }
        if (name2Interaction.get(interactionName).size() > 1) {
            throw new InteractionDuplicatedException(interactionName);
        }
    }

    /**
     * 获取参与对象数
     *
     * @param interactionName 交互名称
     * @return 参与对象数
     * @throws InteractionNotFoundException   交互未找到
     * @throws InteractionDuplicatedException 交互重名
     */
    public int getParticipantCount(String interactionName) throws
            InteractionNotFoundException, InteractionDuplicatedException {
        checkInteractionName(interactionName);

        MyUmlInteraction myUmlInteraction =
                name2Interaction.get(interactionName).get(0);
        return myUmlInteraction.getParticipantCount();
    }

    /**
     * 获取消息数
     *
     * @param interactionName 交互名称
     * @return 消息数
     * @throws InteractionNotFoundException   交互未找到
     * @throws InteractionDuplicatedException 交互重名
     */
    public int getMessageCount(String interactionName) throws
            InteractionNotFoundException, InteractionDuplicatedException {
        checkInteractionName(interactionName);

        MyUmlInteraction myUmlInteraction =
                name2Interaction.get(interactionName).get(0);
        return myUmlInteraction.getMessageCount();
    }

    /**
     * 获取对象的进入消息数
     *
     * @param interactionName 交互名称
     * @param lifelineName    消息名称
     * @return 进入消息数
     * @throws InteractionNotFoundException   交互未找到
     * @throws InteractionDuplicatedException 交互重名
     * @throws LifelineNotFoundException      生命线未找到
     * @throws LifelineDuplicatedException    生命线重名
     */
    public int getIncomingMessageCount(
            String interactionName, String lifelineName)
            throws InteractionNotFoundException, InteractionDuplicatedException,
            LifelineNotFoundException, LifelineDuplicatedException {
        checkInteractionName(interactionName);

        MyUmlInteraction myUmlInteraction =
                name2Interaction.get(interactionName).get(0);
        return myUmlInteraction.getIncomingMessageCount(
                interactionName, lifelineName);
    }
}
