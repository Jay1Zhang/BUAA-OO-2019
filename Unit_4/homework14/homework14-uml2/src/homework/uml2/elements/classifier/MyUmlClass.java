package homework.uml2.elements.classifier;

import com.oocourse.uml2.interact.common.AttributeClassInformation;
import com.oocourse.uml2.interact.common.AttributeQueryType;
import com.oocourse.uml2.interact.common.OperationQueryType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlClass;
import homework.uml2.elements.meta.MyUmlAttribute;
import homework.uml2.elements.meta.MyUmlOperation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class MyUmlClass extends MyUmlClassifier {
    private MyUmlClass parentClass;
    private HashMap<String, MyUmlInterface> id2Interface; // 本类所实现的接口
    private ArrayList<String> interfaceIdList;  // 可能会有重复，故新增list
    private Answer answer = new Answer();  // 存储答案
    // 在检查R002时，类的自继承也算循环继承，故需要打个标记
    private boolean isSelfInherited = false;

    public MyUmlClass() {}

    public MyUmlClass(UmlClass umlClass) {
        super(umlClass);
        this.parentClass = this;
        this.id2Interface = new HashMap<>();
        this.interfaceIdList = new ArrayList<>();
    }

    public boolean isSelfInherited() {
        return isSelfInherited;
    }

    public void setParentClass(MyUmlClass parentClass) {
        this.parentClass = parentClass;
        // 判断是否是自继承
        if (parentClass.equals(this)) {
            isSelfInherited = true;
        }
    }

    public void setImplementedInterface(MyUmlInterface myUmlInterface) {
        String id = myUmlInterface.getId();
        id2Interface.put(id, myUmlInterface);
        interfaceIdList.add(id);
    }

    public MyUmlClassifier getParentClass() {
        return parentClass;
    }

    /**
     * 类中的属性有多少个
     * - `ALL` 全部属性数量（包括各级父类定义的属性）
     * - `SELF_ONLY` 此类自身定义的属性数量
     * @param mode
     * @return
     */
    public int getAttrCnt(AttributeQueryType mode) {
        /* if - SELF_ONLY */
        if (mode.equals(AttributeQueryType.SELF_ONLY)) {
            return super.getName2Attr().size();
        }
        /* else - ALL */
        if (answer.getAllAttrCnt() != -1) {
            // 若已经统计过父类属性数量，直接返回即可，无需继续递归
            return answer.getAllAttrCnt();
        }
        // 递归查找 - 若到达顶层
        if (this.equals(parentClass)) {
            answer.setAllAttrCnt(super.getName2Attr().size());
            return answer.getAllAttrCnt();
        }
        int parentAttrCnt = parentClass.getAttrCnt(AttributeQueryType.ALL);
        int thisAttrCnt = super.getName2Attr().size();
        // 保存此类及父类的 ALL - attrCnt
        answer.setAllAttrCnt(parentAttrCnt + thisAttrCnt);
        return answer.getAllAttrCnt();
    }

    /**
     * 类中的操作有多少个
     * 本指令中统计的一律为此类自己定义的操作，不包含其各级父类所定义的操作
     * - `NON_RETURN` 无返回值操作数量
     * - `RETURN` 有返回值操作数量
     * - `NON_PARAM` 无传入参数操作数量
     * - `PARAM` 有传入参数操作数量
     * - `ALL` 全部操作数量
     * @return
     */
    public int getOperationCnt(OperationQueryType mode) {
        if (answer.getOperaCnt() != null) {
            return answer.getOperaCnt().get(mode);
        }
        // 尚未统计过, 计算
        int nonReturnCnt = 0;
        int returnCnt = 0;
        int nonParaCnt = 0;
        int paraCnt = 0;
        int allCnt = 0;

        HashMap<String, HashSet<MyUmlOperation>> name2Opera =
                super.getName2Opera();
        for (String operaName: name2Opera.keySet()) {
            // 若有该operaName,则对应value必不为空
            for (MyUmlOperation operation: name2Opera.get(operaName)) {
                if (!operation.hasReturn()) {
                    nonReturnCnt++;
                } else {
                    returnCnt++;
                }
                if (!operation.hasPara()) {
                    nonParaCnt++;
                } else {
                    paraCnt++;
                }
                allCnt++;
            }
        }

        HashMap<OperationQueryType, Integer> operaCnt = new HashMap<>();
        operaCnt.put(OperationQueryType.NON_RETURN, nonReturnCnt);
        operaCnt.put(OperationQueryType.RETURN, returnCnt);
        operaCnt.put(OperationQueryType.NON_PARAM, nonParaCnt);
        operaCnt.put(OperationQueryType.PARAM, paraCnt);
        operaCnt.put(OperationQueryType.ALL, allCnt);
        // 保存答案
        answer.setOperaCnt(operaCnt);
        return answer.getOperaCnt().get(mode);
    }

    /**
     * 类有几个关联
     * @return
     */
    public int getAssocCnt() {
        if (answer.getAssocCnt() != -1) {
            // 已统计过，直接返回
            return answer.getAssocCnt();
        }

        // 若到达顶层
        if (this.equals(parentClass)) {
            answer.setAssocCnt(super.getId2Assoc().size());
            return answer.getAssocCnt();
        }

        int parentAssocCnt = parentClass.getAssocCnt();
        int thisAssocCnt = super.getId2Assoc().size();

        answer.setAssocCnt(parentAssocCnt + thisAssocCnt);
        return answer.getAssocCnt();
    }

    /**
     * 返回所有关联端的ID
     * @return
     */
    public Set<String> getAssocIdSet() {
        if (answer.getAssocIdSet() != null) {
            return answer.getAssocIdSet();
        }
        // 若到达顶层
        if (this.equals(parentClass)) {
            Set<String> res = new HashSet<>();
            res.addAll(super.getId2Assoc().keySet());

            answer.setAssocIdSet(res);
            return res; // answer.getAssocIdSet();
        }

        Set<String> parentAssocIdList = parentClass.getAssocIdSet();
        Set<String> res = new HashSet<>();
        // 合并父类以及本类关联端的Id
        res.addAll(parentAssocIdList);
        res.addAll(super.getId2Assoc().keySet());

        answer.setAssocIdSet(res);
        return res; // answer.getAssocIdSet();
    }

    /**
     * 类的操作可见性
     * - 本指令中统计的一律为此类自己定义的操作，不包含其各级父类所定义的操作
     * - 在上一条的前提下，需要统计出全部的名为methodName的方法的可见性信息
     * @param methodName
     * @return
     */
    public HashMap<Visibility, Integer> getOperaVis(String methodName) {
        HashMap<Visibility, Integer> res = new HashMap<>();
        res.put(Visibility.PUBLIC, 0);
        res.put(Visibility.PROTECTED, 0);
        res.put(Visibility.PRIVATE, 0);
        res.put(Visibility.PACKAGE, 0);

        HashMap<String, HashSet<MyUmlOperation>> name2Opera =
                super.getName2Opera();
        if (name2Opera.containsKey(methodName)) {
            HashSet<MyUmlOperation> operas = name2Opera.get(methodName);
            for (MyUmlOperation opera: operas) {
                res.merge(opera.getVisibility(), 1,
                    (oldVal, para) -> oldVal + para);
            }
        }
        return res;
    }

    /**
     * 类的属性可见性
     * 本指令的查询均需要考虑属性的继承关系
     * @param attrName
     * @return
     */
    public Visibility getAttrVis(String attrName) {
        if (super.getName2Attr().containsKey(attrName)) {
            return super.getName2Attr().get(attrName).getVisibility();
        }
        // 若本类没有，递归查找
        if (this.equals(parentClass)) {
            return null;
        }
        return parentClass.getAttrVis(attrName);
    }

    public int findAttrCnt(String attrName) {
        if (this.equals(parentClass)) {
            if (super.getName2Attr().containsKey(attrName)) {
                return 1;
            } else {
                return 0;
            }
        }

        int parentAttrCnt = parentClass.findAttrCnt(attrName);
        int thisAttrCnt;
        if (super.getName2Attr().containsKey(attrName)) {
            thisAttrCnt = 1;
        } else {
            thisAttrCnt = 0;
        }

        return thisAttrCnt + parentAttrCnt;
    }

    /**
     * 类的顶级父类
     * @return
     */
    public String getTopParentClass() {
        if (answer.getTopParentClass() != null) {
            return answer.getTopParentClass();
        }

        if (this.equals(parentClass)) {
            answer.setTopParentClass(getName());
            return answer.getTopParentClass(); // getName()
        }

        answer.setTopParentClass(parentClass.getTopParentClass());
        return answer.getTopParentClass(); // parentClass.getTopParentClass()
    }

    /**
     * 类是否违背信息隐藏原则
     * @return
     */
    public List<AttributeClassInformation> getInformationNotHidden() {
        if (answer.getInformationNotHidden() != null) {
            return answer.getInformationNotHidden();
        }

        if (this.equals(parentClass)) {
            List<AttributeClassInformation> res = new ArrayList<>();
            // 遍历属性集合，将非private属性加入List
            for (String attrName: super.getName2Attr().keySet()) {
                MyUmlAttribute myUmlAttribute =
                        super.getName2Attr().get(attrName);
                if (!myUmlAttribute.getVisibility().equals(
                        Visibility.PRIVATE)) {
                    res.add(new AttributeClassInformation(attrName, getName()));
                }
            }

            answer.setInformationNotHidden(res);
            return res;
        }

        List<AttributeClassInformation> parentList =
                parentClass.getInformationNotHidden();
        List<AttributeClassInformation> res = new ArrayList<>();
        // 合并父类非private属性
        res.addAll(parentList);
        // 将本类非private属性加入List
        for (String attrName: super.getName2Attr().keySet()) {
            MyUmlAttribute myUmlAttribute = super.getName2Attr().get(attrName);
            if (!myUmlAttribute.getVisibility().equals(Visibility.PRIVATE)) {
                res.add(new AttributeClassInformation(attrName, getName()));
            }
        }

        answer.setInformationNotHidden(res);
        return res;
    }

    /**
     * 类实现的全部接口Id
     * 特别值得注意的是，无论是直接实现还是通过父类或者接口继承等方式间接实现，都算做实现了接口
     * 故不仅需要遍历父类的接口，还需要遍历每个接口的父接口
     * 参照 getAssocSet() 写法
     * @return
     */
    public Set<String> getInterfaceIdSet() {
        if (answer.getAllInterfaceIdSet() != null) {
            return answer.getAllInterfaceIdSet();
        }

        // 若到达顶层
        if (this.equals(parentClass)) {
            Set<String> res = new HashSet<>();
            res.addAll(id2Interface.keySet());

            answer.setAllInterfaceIdSet(res);
            return answer.getAllInterfaceIdSet();
        }

        Set<String> parentInterfaceIdList = parentClass.getInterfaceIdSet();
        Set<String> res = new HashSet<>();
        res.addAll(parentInterfaceIdList);
        res.addAll(id2Interface.keySet());

        answer.setAllInterfaceIdSet(res);
        return answer.getAllInterfaceIdSet();
    }

    public ArrayList<String> getInterfaceIdList() {
        // 若到达顶层
        if (this.equals(parentClass)) {
            ArrayList<String> res = new ArrayList<>();
            res.addAll(interfaceIdList);

            return res;
        }

        ArrayList<String> parentInterfaceIdList =
                parentClass.getInterfaceIdList();
        ArrayList<String> res = new ArrayList<>();
        res.addAll(parentInterfaceIdList);
        res.addAll(interfaceIdList);

        return res;
    }

    /**
     * 此做法默认了不支持类的多继承
     * @param stClassId
     * @param visited
     * @return
     */
    public boolean isLoop(String stClassId, HashSet<String> visited) {
        // 重复访问有三种可能
        // 1. 此条继承关系链无自环
        // 2. 有自环且 stClass 在环中，形如 0
        // 3. 有自环但 stClass 并不在环中，形如 6
        //          注意由于类无多继承， 6 这个尾巴只能是子类
        if (visited.contains(getId())) {
            if (this.equals(parentClass)) {
                // 1. 到达顶级父类，此条继承关系链无自环
                return false;
            } else if (stClassId.equals(getId())) {
                // 2. 刚好首尾相接，形成闭环，且 stClass 在环中
                return true;
            } else {
                // 3. 其父类形成了闭环，但 stClass 不在环中
                return false;
            }
        }

        visited.add(getId());
        return parentClass.isLoop(stClassId, visited);
    }
}
