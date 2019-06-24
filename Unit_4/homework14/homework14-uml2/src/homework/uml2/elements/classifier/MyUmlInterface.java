package homework.uml2.elements.classifier;

import com.oocourse.uml2.models.elements.UmlInterface;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class MyUmlInterface extends MyUmlClassifier {
    private Set<MyUmlInterface> directParentSet;
    private ArrayList<MyUmlInterface> directParentList; // 可能会有重复，故采用list
    private Set<String> allParentInterfaceIdSet; // 存储答案

    public MyUmlInterface() {}

    public MyUmlInterface(UmlInterface umlInterface) {
        super(umlInterface);
        this.directParentSet = new HashSet<>();
        this.directParentList = new ArrayList<>();
        this.allParentInterfaceIdSet = null;
    }

    public void setParentInterface(MyUmlInterface parentInterface) {
        directParentSet.add(parentInterface);
        directParentList.add(parentInterface);
    }

    public Set<MyUmlInterface> getDirectParentSet() {
        return directParentSet;
    }

    /**
     * 返回该接口及所有父类接口Id
     * @return
     */
    public Set<String> getAllParentInterfaceIdSet() {
        if (allParentInterfaceIdSet != null) {
            return allParentInterfaceIdSet;
        }

        // 若到达顶层
        if (directParentSet.isEmpty()) {
            Set<String> res = new HashSet<>();
            res.add(super.getId());

            allParentInterfaceIdSet = res;
            return allParentInterfaceIdSet;
        }

        Set<String> res = new HashSet<>();
        // 合并所有父类接口
        for (MyUmlInterface parentInterface: directParentSet) {
            Set<String> parentInterfaceIdSet =
                    parentInterface.getAllParentInterfaceIdSet();

            res.addAll(parentInterfaceIdSet);
        }
        res.add(getId());
        allParentInterfaceIdSet = res;
        return allParentInterfaceIdSet;
    }

    /**
     * 此处可能有bug
     *  bug：形如 6 的继承链时，务必注意环外部链上的接口是不需要输出的，已修复。
     * @param stInterfaceId
     * @param visited
     * @return
     */
    public boolean isLoop(String stInterfaceId, HashSet<String> visited) {
        // 由于接口与类的父类实现方式不同，故如果此条继承关系链无自环，则不会重复访问
        // 因而重复访问只有两种可能
        // 1. 有自环且 stInterface 在环中，形如 0
        // 2. 有自环但 stInterface 并不在环中，形如 6
        if (visited.contains(getId())) {
            if (stInterfaceId.equals(getId())) {
                // 1. 自环
                return true;
            } else {
                // 2. 以 stInterface 为起点的继承链无闭环(但链内有自环)
                return false;
            }
        }

        visited.add(getId());
        for (MyUmlInterface myUmlInterface: directParentSet) {
            if (myUmlInterface.isLoop(stInterfaceId, visited)) {
                return true;
            }
        }
        visited.remove(getId());

        return false;
    }

    /**
     * 用于检查 R003
     * 由于可能会有重复继承，故采用list
     * @return
     */
    public ArrayList<String> getAllParentInterfaceIdList() {
        // 若到达顶层
        if (directParentList.isEmpty()) {
            ArrayList<String> res = new ArrayList<>();
            res.add(getId());

            return res;
        }

        ArrayList<String> res = new ArrayList<>();
        // 合并所有父类接口
        for (MyUmlInterface parentInterface: directParentList) {
            ArrayList<String> parentInterfaceIdList =
                    parentInterface.getAllParentInterfaceIdList();

            res.addAll(parentInterfaceIdList);
        }
        res.add(getId());

        return res;
    }
}
