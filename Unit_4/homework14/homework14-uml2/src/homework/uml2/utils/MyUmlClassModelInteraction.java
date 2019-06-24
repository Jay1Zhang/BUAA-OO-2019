package homework.uml2.utils;

import com.oocourse.uml2.interact.common.AttributeClassInformation;
import com.oocourse.uml2.interact.common.AttributeQueryType;
import com.oocourse.uml2.interact.common.OperationQueryType;
import com.oocourse.uml2.interact.exceptions.user.AttributeDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.AttributeNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml2.interact.format.UmlClassModelInteraction;
import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlAssociation;
import com.oocourse.uml2.models.elements.UmlAssociationEnd;
import com.oocourse.uml2.models.elements.UmlAttribute;
import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlGeneralization;
import com.oocourse.uml2.models.elements.UmlInterface;
import com.oocourse.uml2.models.elements.UmlInterfaceRealization;
import com.oocourse.uml2.models.elements.UmlOperation;
import com.oocourse.uml2.models.elements.UmlParameter;
import homework.uml2.elements.meta.MyUmlAssociationEnd;
import homework.uml2.elements.meta.MyUmlAttribute;
import homework.uml2.elements.classifier.MyUmlClass;
import homework.uml2.elements.classifier.MyUmlClassifier;
import homework.uml2.elements.classifier.MyUmlInterface;
import homework.uml2.elements.meta.MyUmlOperation;
import homework.uml2.elements.meta.MyUmlParameter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * UML交互接口
 */
public class MyUmlClassModelInteraction implements UmlClassModelInteraction {
    // UmlClass
    private HashMap<String, MyUmlClass> id2Class = new HashMap<>();
    private HashMap<String, ArrayList<MyUmlClass>> name2Class = new HashMap<>();
    // UmlInterface
    private HashMap<String, MyUmlInterface> id2Interface = new HashMap<>();
    // UmlOperation
    private HashMap<String, MyUmlOperation> id2Operation = new HashMap<>();
    // UmlAssociationEnd
    private HashMap<String, MyUmlAssociationEnd> id2AssocEnd = new HashMap<>();

    public MyUmlClassModelInteraction() {

    }

    public HashMap<String, MyUmlClass> getId2Class() {
        return id2Class;
    }

    public HashMap<String, MyUmlInterface> getId2Interface() {
        return id2Interface;
    }

    public HashMap<String, ArrayList<MyUmlClass>> getName2Class() {
        return name2Class;
    }

    public boolean containsClassOrInterface(String id) {
        if (id2Class.containsKey(id)) {
            return true;
        }
        if (id2Interface.containsKey(id)) {
            return true;
        }
        return false;
    }

    /* 1. ADD CLASS & INTERFACE */
    public void addUmlClass(UmlClass umlClass) {
        MyUmlClass myUmlClass = new MyUmlClass(umlClass);
        String id = umlClass.getId();
        String name = umlClass.getName();
        id2Class.put(id, myUmlClass);

        ArrayList<MyUmlClass> temp;
        if (name2Class.containsKey(name)) {
            temp = name2Class.get(name);
        } else {
            temp = new ArrayList<>();
        }
        temp.add(myUmlClass);
        name2Class.put(name, temp);
    }

    public void addUmlInterface(UmlInterface umlInterface) {
        MyUmlInterface myUmlInterface = new MyUmlInterface(umlInterface);
        String id = umlInterface.getId();
        // add to map
        id2Interface.put(id, myUmlInterface);
    }

    /* 2. ADD attr & opera & end */
    public void addUmlAttribute(UmlAttribute umlAttribute) {
        MyUmlAttribute myUmlAttribute = new MyUmlAttribute(umlAttribute);
        // 映射到所在类或接口
        String clsfrId = myUmlAttribute.getParentId();
        if (id2Class.containsKey(clsfrId)) {
            MyUmlClass myUmlClass = id2Class.get(clsfrId);
            myUmlClass.setAttribute(myUmlAttribute);
        } else {
            MyUmlInterface myUmlInterface = id2Interface.get(clsfrId);
            myUmlInterface.setAttribute(myUmlAttribute);
        }
    }

    public void addUmlOperation(UmlOperation umlOperation) {
        MyUmlOperation myUmlOperation = new MyUmlOperation(umlOperation);
        // add to map
        String id = umlOperation.getId();
        id2Operation.put(id, myUmlOperation);
        // 映射到所在类或接口
        String clsfrId = myUmlOperation.getParentId();
        if (id2Class.containsKey(clsfrId)) {
            MyUmlClass myUmlClass = id2Class.get(clsfrId);
            myUmlClass.setOperation(myUmlOperation);
        } else {
            MyUmlInterface myUmlInterface = id2Interface.get(clsfrId);
            myUmlInterface.setOperation(myUmlOperation);
        }
    }

    public void addUmlAssociationEnd(UmlAssociationEnd umlAssociationEnd) {
        MyUmlAssociationEnd myUmlAssociationEnd =
                new MyUmlAssociationEnd(umlAssociationEnd);
        // add to map
        String id = umlAssociationEnd.getId();
        id2AssocEnd.put(id, myUmlAssociationEnd);
        // set name & type
        String refId = myUmlAssociationEnd.getReference();
        if (id2Class.containsKey(refId)) {
            MyUmlClass myUmlClass = id2Class.get(refId);
            myUmlAssociationEnd.setName(myUmlClass.getName());
            myUmlAssociationEnd.setUmlType(myUmlClass.getElementType());
        } else {
            MyUmlInterface myUmlInterface = id2Interface.get(refId);
            myUmlAssociationEnd.setName(myUmlInterface.getName());
            myUmlAssociationEnd.setUmlType(myUmlInterface.getElementType());
        }
    }

    /* 3. ADD para & association & generation & realization */
    public void addUmlParameter(UmlParameter umlParameter) {
        MyUmlParameter myUmlParameter = new MyUmlParameter(umlParameter);
        // 映射到所在方法
        String methodId = myUmlParameter.getParentId();
        MyUmlOperation myUmlOperation = id2Operation.get(methodId);
        myUmlOperation.setPara(myUmlParameter);
    }

    public void addUmlAssociation(UmlAssociation umlAssociation) {
        String end1Id = umlAssociation.getEnd1();
        String end2Id = umlAssociation.getEnd2();
        MyUmlAssociationEnd assocEnd1 = id2AssocEnd.get(end1Id);
        MyUmlAssociationEnd assocEnd2 = id2AssocEnd.get(end2Id);

        MyUmlClassifier clsfr1;
        if (id2Class.containsKey(assocEnd1.getReference())) {
            clsfr1 = id2Class.get(assocEnd1.getReference());
        } else {
            clsfr1 = id2Interface.get(assocEnd1.getReference());
        }
        clsfr1.setAssociation(assocEnd2);

        MyUmlClassifier clsfr2;
        if (id2Class.containsKey(assocEnd2.getReference())) {
            clsfr2 = id2Class.get(assocEnd2.getReference());
        } else {
            clsfr2 = id2Interface.get(assocEnd2.getReference());
        }
        clsfr2.setAssociation(assocEnd1);
    }

    public void addUmlGeneralization(UmlGeneralization umlGeneralization) {
        String childId = umlGeneralization.getSource();
        String parentId = umlGeneralization.getTarget();

        if (id2Class.containsKey(childId)) {
            MyUmlClass childClass = id2Class.get(childId);
            MyUmlClass parentClass = id2Class.get(parentId);
            childClass.setParentClass(parentClass);
        } else {
            MyUmlInterface childInterf = id2Interface.get(childId);
            MyUmlInterface parentInterf = id2Interface.get(parentId);
            childInterf.setParentInterface(parentInterf);
        }
    }

    void addUmlInterfaceRealization(
             UmlInterfaceRealization umlInterfaceRealization) {
        String classId = umlInterfaceRealization.getSource();
        String interfaceId = umlInterfaceRealization.getTarget();

        MyUmlClass myUmlClass = id2Class.get(classId);
        MyUmlInterface myUmlInterface = id2Interface.get(interfaceId);

        myUmlClass.setImplementedInterface(myUmlInterface);
    }

    private void checkClassName(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!name2Class.containsKey(className)) {
            throw new ClassNotFoundException(className);
        }
        if (name2Class.get(className).size() != 1) {
            throw new ClassDuplicatedException(className);
        }
    }

    /**
     * 获取类数量
     * 指令：CLASS_COUNT
     *
     * @return 类数量
     */
    public int getClassCount() {
        return id2Class.size();
    }

    /**
     * 获取类操作数量
     * 指令：CLASS_OPERATION_COUNT
     *
     * @param className 类名
     * @param queryType 操作类型
     * @return 指定类型的操作数量
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    public int getClassOperationCount(String className,
                                      OperationQueryType queryType)
            throws ClassNotFoundException, ClassDuplicatedException {
        checkClassName(className);

        MyUmlClass myUmlClass = name2Class.get(className).get(0);
        return myUmlClass.getOperationCnt(queryType);
    }

    /**
     * 获取类属性数量
     * 指令：CLASS_ATTR_COUNT
     *
     * @param className 类名
     * @param queryType 操作类型
     * @return 指定类型的操作数量
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    public int getClassAttributeCount(String className,
                                      AttributeQueryType queryType)
            throws ClassNotFoundException, ClassDuplicatedException {
        checkClassName(className);

        MyUmlClass myUmlClass = name2Class.get(className).get(0);
        return myUmlClass.getAttrCnt(queryType);
    }

    /**
     * 获取类关联数量
     * 指令：CLASS_ASSO_COUNT
     *
     * @param className 类名
     * @return 类关联数量
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    public int getClassAssociationCount(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        checkClassName(className);

        MyUmlClass myUmlClass = name2Class.get(className).get(0);
        return myUmlClass.getAssocCnt();
    }

    /**
     * 获取与类相关联的类列表
     * 指令：CLASS_ASSO_CLASS_LIST
     *
     * @param className 类名
     * @return 与类关联的列表
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    public List<String> getClassAssociatedClassList(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        checkClassName(className);

        MyUmlClass myUmlClass = name2Class.get(className).get(0);
        Set<String> assocIdSet = myUmlClass.getAssocIdSet();
        Set<String> assocRefIdSet = getAssocRefIdSet(assocIdSet);

        List<String> assocNameList = new ArrayList<>();
        for (String id: assocRefIdSet) {
            assocNameList.add(id2Class.get(id).getName());
        }
        return assocNameList;
    }

    /**
     * 通过所有的关联端id得到相应的class的Id
     * 保证结果 不重不漏
     * @param assocIdSet
     * @return
     */
    private Set<String> getAssocRefIdSet(Set<String> assocIdSet) {
        Set<String> res = new HashSet<>();
        for (String endId: assocIdSet) {
            MyUmlAssociationEnd assocEnd = id2AssocEnd.get(endId);
            if (assocEnd.getUmlType().equals(ElementType.UML_CLASS)) {
                String refId = assocEnd.getReference();
                res.add(refId);
            }
        }
        return res;
    }

    /**
     * 统计类操作可见性
     * 指令：CLASS_OPERATION_VISIBILITY
     *
     * @param className     类名
     * @param operationName 操作名
     * @return 类操作可见性统计结果
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    public Map<Visibility, Integer> getClassOperationVisibility(
            String className, String operationName)
            throws ClassNotFoundException, ClassDuplicatedException {
        checkClassName(className);

        MyUmlClass myUmlClass = name2Class.get(className).get(0);
        return myUmlClass.getOperaVis(operationName);
    }

    /**
     * 获取类属性可见性
     * 指令：CLASS_ATTR_VISIBILITY
     *
     * @param className     类名
     * @param attributeName 属性名
     * @return 属性可见性
     * @throws ClassNotFoundException       类未找到异常
     * @throws ClassDuplicatedException     类重复异常
     * @throws AttributeNotFoundException   属性未找到异常
     * @throws AttributeDuplicatedException 属性重复异常
     */
    public Visibility getClassAttributeVisibility(String className,
                                                  String attributeName)
            throws ClassNotFoundException, ClassDuplicatedException,
            AttributeNotFoundException, AttributeDuplicatedException {
        checkClassName(className);

        MyUmlClass myUmlClass = name2Class.get(className).get(0);
        int attrCnt = myUmlClass.findAttrCnt(attributeName);
        if (attrCnt == 0) {
            throw new AttributeNotFoundException(className, attributeName);
        } else if (attrCnt > 1) {
            throw new AttributeDuplicatedException(className, attributeName);
        } else {
            // attrCnt == 1;
            return myUmlClass.getAttrVis(attributeName);
        }
    }

    /**
     * 获取顶级父类
     * 指令：CLASS_TOP_BASE
     *
     * @param className 类名
     * @return 顶级父类名
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    public String getTopParentClass(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        checkClassName(className);

        MyUmlClass myUmlClass = name2Class.get(className).get(0);
        return myUmlClass.getTopParentClass();
    }

    /**
     * 获取实现的接口列表
     * 指令：CLASS_IMPLEMENT_INTERFACE_LIST
     *
     * @param className 类名
     * @return 实现的接口列表
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    public List<String> getImplementInterfaceList(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        checkClassName(className);

        MyUmlClass myUmlClass = name2Class.get(className).get(0);

        Set<String> implementInterIdSet = myUmlClass.getInterfaceIdSet();
        Set<String> allInterfaceIdSet =
                getAllInterfaceIdSet(implementInterIdSet);

        List<String> res = new ArrayList<>();
        for (String id: allInterfaceIdSet) {
            res.add(id2Interface.get(id).getName());
        }
        return res;
    }

    /**
     * 通过类实现的接口列表，遍历所有接口，
     * 保证返回结果 不重不漏
     * @param implementInterIdSet
     * @return
     */
    private Set<String> getAllInterfaceIdSet(Set<String> implementInterIdSet) {
        Set<String> res = new HashSet<>();
        for (String id: implementInterIdSet) {
            MyUmlInterface myUmlInterface = id2Interface.get(id);
            Set<String> interfaceIdSet =
                    myUmlInterface.getAllParentInterfaceIdSet();

            res.addAll(interfaceIdSet);
        }
        return res;
    }

    /**
     * 获取类中未隐藏的属性
     * 即违背了面向对象设计中的隐藏信息原则的属性
     * 指令：CLASS_INFO_HIDDEN
     *
     * @param className 类名
     * @return 未隐藏的属性信息列表
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    public List<AttributeClassInformation> getInformationNotHidden(
            String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        checkClassName(className);

        MyUmlClass myUmlClass = name2Class.get(className).get(0);
        return myUmlClass.getInformationNotHidden();
    }

    /**
     * 专用于检查R003规则：
     *      通过类实现的接口列表，遍历所有接口;
     *      保证返回结果 不漏
     * @param implementInterIdList
     * @return
     */
    public ArrayList<String> getAllInterfaceIdList(
            ArrayList<String> implementInterIdList) {
        ArrayList<String> res = new ArrayList<>();
        for (String id: implementInterIdList) {
            MyUmlInterface myUmlInterface = id2Interface.get(id);
            ArrayList<String> interfaceIdList =
                    myUmlInterface.getAllParentInterfaceIdList();

            res.addAll(interfaceIdList);
        }
        return res;
    }
}
