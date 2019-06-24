package homework.uml2.elements.state;

import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlState;
import homework.uml2.elements.MyUmlElement;

import java.util.HashSet;

public class MyUmlState extends MyUmlElement {
    private UmlState umlState;
    private HashSet<MyUmlState> nextStateSet;
    private HashSet<MyUmlFinalState> finalStateSet;
    // private int kind;

    public MyUmlState() {}

    public MyUmlState(UmlState umlState) {
        super(umlState);
        this.umlState = umlState;
        this.nextStateSet = new HashSet<>();
        this.finalStateSet = new HashSet<>();
    }

    public Visibility getVisibility() {
        return umlState.getVisibility();
    }

    public void setNextState(MyUmlState myUmlState) {
        nextStateSet.add(myUmlState);
    }

    public void setFinalState(MyUmlFinalState myUmlFinalState) {
        finalStateSet.add(myUmlFinalState);
    }

    public HashSet<String> getSubsequentState() {
        HashSet<String> visited = new HashSet<>();
        return getReachableState(visited);
    }

    private HashSet<String> getReachableState(HashSet<String> visited) {
        // 若到达顶层
        if (visited.contains(getId())) {
            HashSet<String> res = new HashSet<>();
            res.add(getId());
            return res;
        }
        visited.add(getId());

        // 合并所有next 及 final
        HashSet<String> res = new HashSet<>();
        for (MyUmlState myUmlState: nextStateSet) {
            res.add(myUmlState.getId());
            HashSet<String> temp = myUmlState.getReachableState(visited);
            res.addAll(temp);
        }
        for (MyUmlFinalState myUmlFinalState: finalStateSet) {
            res.add(myUmlFinalState.getId());
            visited.add(myUmlFinalState.getId());
        }

        return res;
    }

    /*
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }

        if (obj == null || this.getClass() != obj.getClass()) {
            return false;
        }

        // 有 Pseudostate, State, FinalState 三种可能的类型
        MyUmlState that = (MyUmlState) obj;
        if (!this.getElementType().equals(that.getElementType())) {
            return false;
        }

        return this.getSelf().equals(that.getSelf());
    }
    */
}
