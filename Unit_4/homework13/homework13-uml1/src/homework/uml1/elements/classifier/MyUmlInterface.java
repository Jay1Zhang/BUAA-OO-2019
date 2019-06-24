package homework.uml1.elements.classifier;

import com.oocourse.uml1.models.elements.UmlInterface;

import java.util.HashSet;
import java.util.Set;

public class MyUmlInterface extends MyUmlClassifier {
    private Set<MyUmlInterface> directParentSet;
    private Set<String> allParentInterfaceIdSet; // 存储答案

    public MyUmlInterface() {}

    public MyUmlInterface(UmlInterface umlInterface) {
        super(umlInterface);
        this.directParentSet = new HashSet<>();
        this.allParentInterfaceIdSet = null;
    }

    public void setParentInterface(MyUmlInterface parentInterface) {
        directParentSet.add(parentInterface);
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

}
