package homework.uml2.utils;

import com.oocourse.uml2.interact.common.AttributeClassInformation;
import com.oocourse.uml2.interact.exceptions.user.UmlRule002Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule008Exception;
import com.oocourse.uml2.interact.exceptions.user.UmlRule009Exception;
import com.oocourse.uml2.interact.format.UmlStandardPreCheck;
import com.oocourse.uml2.models.elements.UmlClass;
import com.oocourse.uml2.models.elements.UmlClassOrInterface;
import com.oocourse.uml2.models.elements.UmlInterface;
import homework.uml2.elements.classifier.MyUmlClass;
import homework.uml2.elements.classifier.MyUmlInterface;
import homework.uml2.elements.meta.MyUmlAssociationEnd;
import homework.uml2.elements.meta.MyUmlAttribute;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

/**
 * UML基本标准预检查
 */
public class MyUmlStandardPreCheck implements UmlStandardPreCheck {
    private final MyUmlClassModelInteraction classModel;

    public MyUmlStandardPreCheck(
            MyUmlClassModelInteraction myUmlClassModelInteraction) {
        this.classModel = myUmlClassModelInteraction;
    }

    /**
     * 检查UML002 规则
     *
     * @throws UmlRule002Exception 规则异常
     */
    public void checkForUml002() throws UmlRule002Exception {
        HashSet<AttributeClassInformation> exceptionInfo = new HashSet<>();
        HashMap<String, MyUmlClass> id2Class = classModel.getId2Class();
        // 这里可能会出现类重名的情况， 故应采用id作为唯一标识
        for (String classId: id2Class.keySet()) {
            MyUmlClass myUmlClass = id2Class.get(classId);
            String className = myUmlClass.getName();
            
            HashMap<String, MyUmlAttribute> id2Attr = myUmlClass.getId2Attr();
            HashMap<String, MyUmlAssociationEnd> id2Assoc =
                    myUmlClass.getId2Assoc();

            HashSet<String> temp = new HashSet<>();
            // 1. 遍历id2Attr
            for (String attrId: id2Attr.keySet()) {
                String name = id2Attr.get(attrId).getName();

                if (temp.contains(name)) {
                    exceptionInfo.add(
                            new AttributeClassInformation(name, className));
                }
                temp.add(name);
            }

            // 2. 遍历id2assoc
            for (String assocId: id2Assoc.keySet()) {
                String name = id2Assoc.get(assocId).getName();
                if (name == null) {
                    continue;
                }

                // 经验证,由于是set，故这里会自动去重
                if (temp.contains(name)) {
                    exceptionInfo.add(
                            new AttributeClassInformation(name, className));
                }
                temp.add(name);
            }
        }

        if (!exceptionInfo.isEmpty()) {
            throw new UmlRule002Exception(exceptionInfo);
        }
    }

    /**
     * 检查UML008 规则
     *
     * @throws UmlRule008Exception 规则异常
     */
    public void checkForUml008() throws UmlRule008Exception {
        HashMap<String, MyUmlClass> id2Class = classModel.getId2Class();
        HashMap<String, MyUmlInterface> id2Interface =
                classModel.getId2Interface();
        HashSet<String> visited = new HashSet<>();

        // 1. 检查类是否循环继承
        HashSet<String> classes = new HashSet<>();
        for (String id: id2Class.keySet()) {
            if (classes.contains(id)) {
                continue;
            }

            MyUmlClass myUmlClass = id2Class.get(id);
            // 1.1 优先判断该类是否为自继承
            if (myUmlClass.isSelfInherited()) {
                classes.add(myUmlClass.getId());
                continue;
            }
            // 1.2 再检查继承链是否为闭环
            visited.clear(); // 清空 visited
            if (myUmlClass.isLoop(id, visited)) {
                classes.addAll(visited);
            }
        }
        // 2. 检查接口是否循环继承
        HashSet<String> interfaces = new HashSet<>();
        for (String id: id2Interface.keySet()) {
            if (interfaces.contains(id)) {
                continue;
            }

            visited.clear(); // 清空 visited
            MyUmlInterface myUmlInterface = id2Interface.get(id);
            if (myUmlInterface.isLoop(id, visited)) {
                interfaces.addAll(visited);
            }
        }

        if (classes.isEmpty() && interfaces.isEmpty()) {
            return;
        } else {
            HashSet<UmlClassOrInterface> res = new HashSet<>();
            for (String id: classes) {
                MyUmlClass myUmlClass = id2Class.get(id);
                res.add((UmlClass) myUmlClass.getSelf());
            }
            for (String id: interfaces) {
                MyUmlInterface myUmlInterface = id2Interface.get(id);
                res.add((UmlInterface) myUmlInterface.getSelf());
            }

            throw new UmlRule008Exception(res);
        }
    }

    /**
     * 检查UML009 规则
     *
     * 重复继承的情况最为复杂，需要检查是否有
     * 0. 类重复继承
     *      由于不支持类的多继承，故类的重复继承体现为循环继承
     * 1. 接口重复继承
     * 2. 类实现了 "重复继承" 的接口
     *      2.1 一个类直接实现了某个 "重复继承" 的接口
     *      2.2 一个类的父类实现了某个 "重复继承" 的接口
     * 3. 类实现了 "重复" 的接口
     *      3.1 一个类直接实现了两个 "重名" 的接口: C1 implement I1, I1
     *      3.2 一个类实现了一个接口和这个接口的父类: C1 implement I1,I2 && I2 extends I1
     *      3.3 一个类与其父类都实现了同一个接口:
     *                      C1 implement I1 && C2 implement I1 && C2 extends C1
     * @throws UmlRule009Exception 规则异常
     */
    public void checkForUml009() throws UmlRule009Exception {
        HashMap<String, MyUmlClass> id2Class = classModel.getId2Class();
        HashMap<String, MyUmlInterface> id2Interface =
                classModel.getId2Interface();
        // 1. 类的 "重复继承"
        //      由于不支持类的多继承，故类的重复继承体现为循环继承
        // 2. 接口的 "重复继承"
        //    与循环不同的是，这里必须遍历所有的接口
        HashSet<String> interfaces = new HashSet<>();
        for (String id: id2Interface.keySet()) {
            MyUmlInterface myUmlInterface = id2Interface.get(id);
            ArrayList<String> allParentIdList =
                    myUmlInterface.getAllParentInterfaceIdList();

            if (isDuplicated(allParentIdList)) {
                interfaces.add(id);
            }
        }


        HashSet<String> classes = new HashSet<>();
        // 3. 检查类是否实现了 "重复接口"
        // 4. 检查类是否实现了 "重复继承" 的接口
        for (String classId: id2Class.keySet()) {
            MyUmlClass myUmlClass = id2Class.get(classId);
            // 这是类直接实现与通过父类继承实现的接口
            ArrayList<String> implementInterfaceIdList =
                    myUmlClass.getInterfaceIdList();
            // 这是类实现的所有接口Id，包括接口本身的继承关系
            ArrayList<String> allImplementInterfaceIdList =
                    classModel.getAllInterfaceIdList(implementInterfaceIdList);

            // 通过类实现的所有接口列表，检查类是否重复实现接口
            if (isDuplicated(allImplementInterfaceIdList)) {
                classes.add(classId);
                continue;   // 如果已判定，直接继续遍历下一个类
            }

            // 遍历所有 "重复继承" 的接口
            for (String interfaceId: interfaces) {
                // 如果实现了该接口，则该类算作 "重复继承"
                if (allImplementInterfaceIdList.contains(interfaceId)) {
                    classes.add(classId);
                    break;
                }
            }
        }

        if (classes.isEmpty() && interfaces.isEmpty()) {
            return;
        } else {
            HashSet<UmlClassOrInterface> res = new HashSet<>();
            for (String id: classes) {
                MyUmlClass myUmlClass = id2Class.get(id);
                res.add((UmlClass) myUmlClass.getSelf());
            }
            for (String id: interfaces) {
                MyUmlInterface myUmlInterface = id2Interface.get(id);
                res.add((UmlInterface) myUmlInterface.getSelf());
            }

            throw new UmlRule009Exception(res);
        }
    }

    public boolean isDuplicated(ArrayList<String> idList) {
        HashSet<String> visited = new HashSet<>();

        for (int i = 0; i < idList.size(); i++) {
            String id = idList.get(i);
            if (visited.contains(id)) {
                return true;
            }
            visited.add(id);
        }
        return false;
    }
}
