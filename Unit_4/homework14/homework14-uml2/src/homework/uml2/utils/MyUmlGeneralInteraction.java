package homework.uml2.utils;

import com.oocourse.uml2.interact.common.AttributeClassInformation;
import com.oocourse.uml2.interact.common.AttributeQueryType;
import com.oocourse.uml2.interact.common.OperationQueryType;
import com.oocourse.uml2.interact.exceptions.user.AttributeDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.AttributeNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.InteractionDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.InteractionNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.UmlRule002Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule008Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule009Exception;
import com.oocourse.uml2.interact.format.UmlGeneralInteraction;
import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlAssociation;
import com.oocourse.uml2.models.elements.UmlAssociationEnd;
import com.oocourse.uml2.models.elements.UmlAttribute;
import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlFinalState;
import com.oocourse.uml2.models.elements.UmlGeneralization;
import com.oocourse.uml2.models.elements.UmlInteraction;
import com.oocourse.uml2.models.elements.UmlInterface;
import com.oocourse.uml2.models.elements.UmlInterfaceRealization;
import com.oocourse.uml2.models.elements.UmlLifeline;
import com.oocourse.uml2.models.elements.UmlMessage;
import com.oocourse.uml2.models.elements.UmlOperation;
import com.oocourse.uml2.models.elements.UmlParameter;
import com.oocourse.uml2.models.elements.UmlPseudostate;
import com.oocourse.uml2.models.elements.UmlRegion;
import com.oocourse.uml2.models.elements.UmlState;
import com.oocourse.uml2.models.elements.UmlStateMachine;
import com.oocourse.uml2.models.elements.UmlTransition;

import java.util.List;
import java.util.Map;

public class MyUmlGeneralInteraction implements UmlGeneralInteraction {
    private final MyUmlClassModelInteraction classModel =
            new MyUmlClassModelInteraction();
    private final MyUmlStateChartInteraction stateChart =
            new MyUmlStateChartInteraction();
    private final MyUmlCollaborationInteraction collaboration =
            new MyUmlCollaborationInteraction();
    private final MyUmlStandardPreCheck stdPreCheck =
            new MyUmlStandardPreCheck(classModel);

    public MyUmlGeneralInteraction(UmlElement... elements) {
        // UmlClass or UmlInterface
        for (int i = 0; i < elements.length; i++) {
            UmlElement element = elements[i];
            ElementType elementType = element.getElementType();
            switch (elementType) {
                case UML_STATE_MACHINE:
                    // add to state chart
                    stateChart.addStateMachine((UmlStateMachine) element);
                    break;
                case UML_REGION:
                    // add to state chart
                    stateChart.addRegion((UmlRegion) element);
                    break;
                case UML_INTERACTION:
                    // add to Collaboration
                    collaboration.addInteraction((UmlInteraction) element);
                    break;
                case UML_CLASS:
                    classModel.addUmlClass((UmlClass) element);
                    break;
                case UML_INTERFACE:
                    classModel.addUmlInterface((UmlInterface) element);
                    break;
                default:
                    break;
            }
        }
        // Attribute or Operation or AssociationEnd
        // plus Interaction or Attribute(type:{""})
        for (int i = 0; i < elements.length; i++) {
            UmlElement element = elements[i];
            ElementType elementType = element.getElementType();
            switch (elementType) {
                case UML_PSEUDOSTATE:
                    // add to state chart
                    stateChart.addPseudostate((UmlPseudostate) element);
                    break;
                case UML_STATE:
                    // add to state chart
                    stateChart.addState((UmlState) element);
                    break;
                case UML_FINAL_STATE:
                    // add to state chart
                    stateChart.addFinalState((UmlFinalState) element);
                    break;
                case UML_LIFELINE:
                    // add to Collaboration
                    collaboration.addLifeline((UmlLifeline) element);
                    break;
                case UML_ATTRIBUTE:
                    String parentId = element.getParentId();
                    if (classModel.containsClassOrInterface(parentId)) {
                        classModel.addUmlAttribute((UmlAttribute) element);
                    } else {
                        // type:{""} - add to Collaboration
                        collaboration.addRole((UmlAttribute) element);
                    }
                    break;
                case UML_OPERATION:
                    classModel.addUmlOperation((UmlOperation) element);
                    break;
                case UML_ASSOCIATION_END:
                    classModel.addUmlAssociationEnd(
                            (UmlAssociationEnd) element);
                    break;
                default:
                    break;
            }
        }
        // Generalization or Association or interfaceRealization or Parameter
        for (int i = 0; i < elements.length; i++) {
            UmlElement element = elements[i];
            ElementType elementType = element.getElementType();

            switch (elementType) {
                case UML_TRANSITION:
                    // add to state chart
                    stateChart.addTransition((UmlTransition) element);
                    break;
                case UML_EVENT:
                    // add to state chart
                    // there is no need to add UmlEvent.
                    // if add, attention the order of UmlTransition & UmlEvent
                    break;
                case UML_MESSAGE:
                    // add to Collaboration
                    collaboration.addMessage((UmlMessage) element);
                    break;
                case UML_PARAMETER:
                    classModel.addUmlParameter((UmlParameter) element);
                    break;
                case UML_ASSOCIATION:
                    classModel.addUmlAssociation((UmlAssociation) element);
                    break;
                case UML_GENERALIZATION:
                    classModel.addUmlGeneralization(
                            (UmlGeneralization) element);
                    break;
                case UML_INTERFACE_REALIZATION:
                    classModel.addUmlInterfaceRealization(
                            (UmlInterfaceRealization) element);
                    break;
                default:
                    break;
            }
        }
    }

    /**
     * MyUmlClassModelInteraction
     * - finished
     * - checked
     */
    public int getClassCount() {
        return classModel.getClassCount();
    }

    public int getClassOperationCount(
            String className, OperationQueryType queryType)
            throws ClassNotFoundException, ClassDuplicatedException {
        return classModel.getClassOperationCount(className, queryType);
    }

    public int getClassAttributeCount(
            String className, AttributeQueryType queryType)
            throws ClassNotFoundException, ClassDuplicatedException {
        return classModel.getClassAttributeCount(className, queryType);
    }

    public int getClassAssociationCount(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        return classModel.getClassAssociationCount(className);
    }

    public List<String> getClassAssociatedClassList(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        return classModel.getClassAssociatedClassList(className);
    }

    public Map<Visibility, Integer> getClassOperationVisibility(
            String className, String operationName)
            throws ClassNotFoundException, ClassDuplicatedException {
        return classModel.getClassOperationVisibility(className, operationName);
    }

    public Visibility getClassAttributeVisibility(
            String className, String attributeName)
            throws ClassNotFoundException, ClassDuplicatedException,
            AttributeNotFoundException, AttributeDuplicatedException {
        return classModel.getClassAttributeVisibility(className, attributeName);
    }

    public String getTopParentClass(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        return classModel.getTopParentClass(className);
    }

    public List<String> getImplementInterfaceList(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        return classModel.getImplementInterfaceList(className);
    }

    public List<AttributeClassInformation> getInformationNotHidden(
            String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        return classModel.getInformationNotHidden(className);
    }

    /**
     * MyUmlStandardPreCheck
     */
    public void checkForUml002() throws UmlRule002Exception {
        stdPreCheck.checkForUml002();
    }

    public void checkForUml008() throws UmlRule008Exception {
        stdPreCheck.checkForUml008();
    }

    public void checkForUml009() throws UmlRule009Exception {
        stdPreCheck.checkForUml009();
    }

    /**
     * MyUmlStateChartInteraction
     * - finished
     * - checked
     */
    public int getStateCount(String stateMachineName) throws
            StateMachineNotFoundException, StateMachineDuplicatedException {
        return stateChart.getStateCount(stateMachineName);
    }

    public int getTransitionCount(String stateMachineName) throws
            StateMachineNotFoundException, StateMachineDuplicatedException {
        return stateChart.getTransitionCount(stateMachineName);
    }

    public int getSubsequentStateCount(
            String stateMachineName, String stateName) throws
            StateMachineNotFoundException, StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException {
        return stateChart.getSubsequentStateCount(stateMachineName, stateName);
    }

    /**
     * MyUmlCollaborationInteraction
     * - finished
     * - checked
     */
    public int getParticipantCount(String interactionName) throws
            InteractionNotFoundException, InteractionDuplicatedException {
        return collaboration.getParticipantCount(interactionName);
    }

    public int getMessageCount(String interactionName) throws
            InteractionNotFoundException, InteractionDuplicatedException {
        return collaboration.getMessageCount(interactionName);
    }

    public int getIncomingMessageCount(
            String interactionName, String lifelineName)
            throws InteractionNotFoundException, InteractionDuplicatedException,
            LifelineNotFoundException, LifelineDuplicatedException {
        return collaboration.getIncomingMessageCount(
                interactionName, lifelineName);
    }
}
