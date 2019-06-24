package homework.uml2.utils;

import com.oocourse.uml2.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateNotFoundException;
import com.oocourse.uml2.interact.format.UmlStateChartInteraction;
import com.oocourse.uml2.models.elements.UmlEvent;
import com.oocourse.uml2.models.elements.UmlFinalState;
import com.oocourse.uml2.models.elements.UmlPseudostate;
import com.oocourse.uml2.models.elements.UmlRegion;
import com.oocourse.uml2.models.elements.UmlState;
import com.oocourse.uml2.models.elements.UmlStateMachine;
import com.oocourse.uml2.models.elements.UmlTransition;
import homework.uml2.elements.interact.MyUmlStateMachine;

import java.util.ArrayList;
import java.util.HashMap;

/**
 * UML状态图交互
 */
public class MyUmlStateChartInteraction implements UmlStateChartInteraction {
    private HashMap<String, UmlRegion> id2Region;
    private HashMap<String, MyUmlStateMachine> id2StateMachine;
    private HashMap<String, ArrayList<MyUmlStateMachine>> name2StateMachine;

    public MyUmlStateChartInteraction() {
        this.id2Region = new HashMap<>();
        this.id2StateMachine = new HashMap<>();
        this.name2StateMachine = new HashMap<>();
    }

    public void addStateMachine(UmlStateMachine umlStateMachine) {
        MyUmlStateMachine myUmlStateMachine =
                new MyUmlStateMachine(umlStateMachine);
        String id = umlStateMachine.getId();
        String name = umlStateMachine.getName();
        id2StateMachine.put(id, myUmlStateMachine);

        ArrayList<MyUmlStateMachine> temp;
        if (name2StateMachine.containsKey(name)) {
            temp = name2StateMachine.get(name);
        } else {
            temp = new ArrayList<>();
        }
        temp.add(myUmlStateMachine);
        name2StateMachine.put(name, temp);
    }

    public void addRegion(UmlRegion umlRegion) {
        id2Region.put(umlRegion.getId(), umlRegion);
    }

    public void addState(UmlState umlState) {
        UmlRegion umlRegion = id2Region.get(umlState.getParentId());
        MyUmlStateMachine myUmlStateMachine =
                id2StateMachine.get(umlRegion.getParentId());
        myUmlStateMachine.addState(umlState);
    }

    public void addPseudostate(UmlPseudostate umlPseudostate) {
        UmlRegion umlRegion = id2Region.get(umlPseudostate.getParentId());
        MyUmlStateMachine myUmlStateMachine =
                id2StateMachine.get(umlRegion.getParentId());
        myUmlStateMachine.addPseudostate(umlPseudostate);
    }

    public void addFinalState(UmlFinalState umlFinalState) {
        UmlRegion umlRegion = id2Region.get(umlFinalState.getParentId());
        MyUmlStateMachine myUmlStateMachine =
                id2StateMachine.get(umlRegion.getParentId());
        myUmlStateMachine.addFinalState(umlFinalState);
    }

    public void addTransition(UmlTransition umlTransition) {
        UmlRegion umlRegion = id2Region.get(umlTransition.getParentId());
        MyUmlStateMachine myUmlStateMachine =
                id2StateMachine.get(umlRegion.getParentId());
        myUmlStateMachine.addTransition(umlTransition);
    }

    public void addEvent(UmlEvent umlEvent) {

    }

    private void checkStateMachineName(String stateMachineName) throws
            StateMachineNotFoundException, StateMachineDuplicatedException {
        if (!name2StateMachine.containsKey(stateMachineName)) {
            throw new StateMachineNotFoundException(stateMachineName);
        }
        if (name2StateMachine.get(stateMachineName).size() > 1) {
            throw new StateMachineDuplicatedException(stateMachineName);
        }
    }

    /**
     * 获取状态机的状态数
     *
     * @param stateMachineName 状态机名称
     * @return 状态数
     * @throws StateMachineNotFoundException   状态机未找到
     * @throws StateMachineDuplicatedException 状态机存在重名
     */
    public int getStateCount(String stateMachineName) throws
            StateMachineNotFoundException, StateMachineDuplicatedException {
        checkStateMachineName(stateMachineName);

        MyUmlStateMachine myUmlStateMachine =
                name2StateMachine.get(stateMachineName).get(0);
        return myUmlStateMachine.getStateCount();
    }

    /**
     * 获取状态机转移数
     *
     * @param stateMachineName 状态机名称
     * @return 转移数
     * @throws StateMachineNotFoundException   状态机未找到
     * @throws StateMachineDuplicatedException 状态机存在重名
     */
    public int getTransitionCount(String stateMachineName) throws
            StateMachineNotFoundException, StateMachineDuplicatedException {
        checkStateMachineName(stateMachineName);

        MyUmlStateMachine myUmlStateMachine =
                name2StateMachine.get(stateMachineName).get(0);
        return myUmlStateMachine.getTransitionCount();
    }

    /**
     * 获取后继状态数
     *
     * @param stateMachineName 状态机名称
     * @param stateName        状态名称
     * @return 后继状态数
     * @throws StateMachineNotFoundException   状态机未找到
     * @throws StateMachineDuplicatedException 状态机存在重名
     * @throws StateNotFoundException          状态未找到
     * @throws StateDuplicatedException        状态存在重名
     */
    public int getSubsequentStateCount(
            String stateMachineName, String stateName) throws
            StateMachineNotFoundException, StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException {
        checkStateMachineName(stateMachineName);

        MyUmlStateMachine myUmlStateMachine =
                name2StateMachine.get(stateMachineName).get(0);
        return myUmlStateMachine.getSubsequentStateCount(
                stateMachineName, stateName);
    }
}
