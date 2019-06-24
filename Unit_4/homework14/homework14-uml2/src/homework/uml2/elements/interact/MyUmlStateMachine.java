package homework.uml2.elements.interact;

import com.oocourse.uml2.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateNotFoundException;
import com.oocourse.uml2.models.elements.UmlFinalState;
import com.oocourse.uml2.models.elements.UmlPseudostate;
import com.oocourse.uml2.models.elements.UmlState;
import com.oocourse.uml2.models.elements.UmlStateMachine;
import com.oocourse.uml2.models.elements.UmlTransition;
import homework.uml2.elements.MyUmlElement;
import homework.uml2.elements.state.MyUmlFinalState;
import homework.uml2.elements.state.MyUmlPseudostate;
import homework.uml2.elements.state.MyUmlState;
import homework.uml2.elements.meta.MyUmlTransition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class MyUmlStateMachine extends MyUmlElement {
    private HashSet<MyUmlTransition> transitions;
    private HashMap<String, MyUmlState> id2State;
    private HashMap<String, ArrayList<MyUmlState>> name2State;
    private HashMap<String, MyUmlPseudostate> id2Pseudostate;   // 规定了最多有1个
    private HashMap<String, MyUmlFinalState> id2FinalState;     // 规定了最多有1个

    public MyUmlStateMachine() {}

    public MyUmlStateMachine(UmlStateMachine umlStateMachine) {
        super(umlStateMachine);
        this.transitions = new HashSet<>();
        this.id2State = new HashMap<>();
        this.name2State = new HashMap<>();
        this.id2Pseudostate = new HashMap<>();
        this.id2FinalState = new HashMap<>();
    }

    public void addState(UmlState umlState) {
        MyUmlState myUmlState = new MyUmlState(umlState);
        String id = umlState.getId();
        String name = umlState.getName();
        id2State.put(id, myUmlState);

        ArrayList<MyUmlState> temp;
        if (name2State.containsKey(name)) {
            temp = name2State.get(name);
        } else {
            temp = new ArrayList<>();
        }
        temp.add(myUmlState);
        name2State.put(name, temp);
    }

    public void addPseudostate(UmlPseudostate umlPseudostate) {
        MyUmlPseudostate myUmlPseudostate =
                new MyUmlPseudostate(umlPseudostate);
        id2Pseudostate.put(myUmlPseudostate.getId(), myUmlPseudostate);
    }

    public void addFinalState(UmlFinalState umlFinalState) {
        MyUmlFinalState myUmlFinalState = new MyUmlFinalState(umlFinalState);
        id2FinalState.put(myUmlFinalState.getId(), myUmlFinalState);
    }

    /**
     * 只需要考虑umlState的后继即可
     * 不需要存 initial的
     * @param umlTransition
     */
    public void addTransition(UmlTransition umlTransition) {
        MyUmlTransition myUmlTransition = new MyUmlTransition(umlTransition);
        transitions.add(myUmlTransition);

        String sourceId = myUmlTransition.getSourceId();
        String targetId = myUmlTransition.getTargetId();

        if (id2State.containsKey(sourceId)) {
            // state ->
            MyUmlState source = id2State.get(sourceId);
            if (id2State.containsKey(targetId)) {
                MyUmlState target = id2State.get(targetId);
                source.setNextState(target);
            } else if (id2FinalState.containsKey(targetId)) {
                MyUmlFinalState myUmlFinalState = id2FinalState.get(targetId);
                source.setFinalState(myUmlFinalState);
            }
        }
        // initial or final ->

    }

    public int getStateCount() {
        return id2State.size() + id2Pseudostate.size() + id2FinalState.size();
    }

    public int getTransitionCount() {
        return transitions.size();
    }

    private void checkStateName(String stateMachineName, String stateName)
            throws StateNotFoundException, StateDuplicatedException {
        if (!name2State.containsKey(stateName)) {
            throw new StateNotFoundException(stateMachineName, stateName);
        }
        if (name2State.get(stateName).size() > 1) {
            throw new StateDuplicatedException(stateMachineName, stateName);
        }
    }

    /**
     * @param stateMachineName
     * @param stateName
     * @return
     * @throws StateNotFoundException
     * @throws StateDuplicatedException
     */
    public int getSubsequentStateCount(
            String stateMachineName, String stateName)
            throws StateNotFoundException, StateDuplicatedException {
        checkStateName(stateMachineName, stateName);

        MyUmlState myUmlState = name2State.get(stateName).get(0);
        return myUmlState.getSubsequentState().size();
    }

}
