package homework.uml2.elements.classifier;

import com.oocourse.uml2.interact.common.AttributeClassInformation;
import com.oocourse.uml2.interact.common.OperationQueryType;

import java.util.HashMap;
import java.util.List;
import java.util.Set;

/**
 * 对于每个 umlClassifier (实际上是 umlClass)
 * 保存其中七个答案，实现记忆化搜索
 * 其中，
 * 类的个数无需保存
 * 类的属性可见性与操作可见性不予保存, 查一次算一次
 */
public class Answer {
    private int allAttrCnt = -1;
    private HashMap<OperationQueryType, Integer> operaCnt = null;
    private int assocCnt = -1;
    private Set<String> assocIdSet = null;
    private String topParentClass = null;
    private List<AttributeClassInformation> informationNotHidden = null;
    private Set<String> allInterfaceIdSet = null; // 类实现的全部接口id,包括父类

    public void setAllAttrCnt(int allAttrCnt) {
        this.allAttrCnt = allAttrCnt;
    }

    public void setOperaCnt(HashMap<OperationQueryType, Integer> operaCnt) {
        this.operaCnt = operaCnt;
    }

    public void setAssocCnt(int assocCnt) {
        this.assocCnt = assocCnt;
    }

    public void setAssocIdSet(Set<String> assocIdSet) {
        this.assocIdSet = assocIdSet;
    }

    public void setTopParentClass(String topParentClass) {
        this.topParentClass = topParentClass;
    }

    public void setInformationNotHidden(
            List<AttributeClassInformation> informationNotHidden) {
        this.informationNotHidden = informationNotHidden;
    }

    public void setAllInterfaceIdSet(Set<String> allInterfaceIdSet) {
        this.allInterfaceIdSet = allInterfaceIdSet;
    }

    public int getAllAttrCnt() {
        return allAttrCnt;
    }

    public HashMap<OperationQueryType, Integer> getOperaCnt() {
        return operaCnt;
    }

    public int getAssocCnt() {
        return assocCnt;
    }

    public Set<String> getAssocIdSet() {
        return assocIdSet;
    }

    public String getTopParentClass() {
        return topParentClass;
    }

    public List<AttributeClassInformation> getInformationNotHidden() {
        return informationNotHidden;
    }

    public Set<String> getAllInterfaceIdSet() {
        return allInterfaceIdSet;
    }
}
