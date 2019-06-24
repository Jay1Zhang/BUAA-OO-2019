# OO第四单元总结

（1）总结本单元两次作业的架构设计  

（2）总结自己在四个单元中架构设计及OO方法理解的演进  

（3）总结自己在四个单元中测试理解与实践的演进

（4）总结自己的课程收获

（5）立足于自己的体会给课程提三个具体改进建议



## 1. 本单元作业架构设计

### 1.1 UML1设计

​	本次作业主要是实现一个UML类图解析器，可以通过输入各种指令来进行类图有关信息的查询，有关`mdj`文件的解析包仍有官方提供，我们只需要对解析出来的**UML各个构成要素**进行**存储与联系**即可。



#### 分析

对于一个一个`UmlElement`，其各个属性含义如下：

- **UMLElement**
  - **visibility**：该元素的可见性
  - **name**：该元素的名字
  - **_type**：该元素的类型
  - **_id**：该元素的id

本次主要包含五种`UmlElement`元素，如下。

- UMLClass
    - **_parent**：对应的是一个特定的值
-UMLAttribute
    - _parent：对应该属性所在的类

- UMLOperation
     - **_parent**：对应的是该操作所在方法的id

- UMLParameter
    - type：该参数的数据类型
    - direction：方向，in-参数；return-返回值


- UMLAssociationEnd
    - reference：该关联端对应的类或接口的ID
    - multiplicity：重复度，该关联端对应类或接口的实例个数
    - aggregation：聚合，暂未使用
- UMLInterface
    - **_parent**：同UMLClass，对应的同一个特定的值

其中，umlClass与umlInterface可直接解析；attribute，operation，parameter 以及associationEnd 由于分别对应了相应的 类，类，操作，类或接口，故有可能会出现在相应parent的前面，造成空指针错误，因而需要在录入时，分多次遍历。

此外，本次作业还包含了三种**元素之间的关系**：


- UMLInterfaceRealization
    - **_parent**：同source
    - source：对应实现该接口的类的ID
    - target：对应该接口的ID
- UMLGeneralization
    - **_parent**：同source，对应子类ID
    - source：对应子类ID
    - target：对应父类ID

- UMLAssociation
  - end1：对应其中一个UMLAssociationEnd的Id
  - end2：对应另外一个UMLAssociationEnd的Id

至此，所有**元素以及元素之间的关系**已经一目了然，我们只需保存相应的元素即可，而关系本身则不需要保存。



#### 架构设计

​	本次作业主要包含两个包：`utils` 和 `elements`。 `utils` 实现了官方要求的`MyUmlInteraction`类 。 `elements`  中均是为了更高的扩展性，基于官方包中的各个`UmlElement` 元素重写的各个 `MyUmlElement`方法。文件树如下：

```
└─homework
    └─uml1
        │  Main.java
        │  
        ├─elements
        │  │  MyUmlElement.java
        │  │  
        │  ├─classifier
        │  │      Answer.java
        │  │      MyUmlClass.java
        │  │      MyUmlClassifier.java
        │  │      MyUmlInterface.java
        │  │      
        │  └─meta
        │          MyUmlAssociationEnd.java
        │          MyUmlAttribute.java
        │          MyUmlOperation.java
        │          MyUmlParameter.java
        │          
        └─utils
                MyUmlInteraction.java
                
```



#### 类设计

##### homework.uml1.utils

- `MyUmlInteraction`
  - 存储了`UmlClass`、`UmlInterace`、`UmlOperation`以及`UmlAssociationEnd`。

##### homework.uml1.elements

- `MyUmlElement`
  - 继承了`UmlElement`
  - 重写了`equals()`以及`hashcode()`方法

- `meta.*`
  - 实现了各个MyUmlElement
  - 其中，`MyUmlOperation`需要保存其相应的`MyUmlParameter`

- `classifier.*`
  - 由于**类与接口**都需要存储相应的**属性，方法，关联对端**，故将其抽象为`MyUmlClassifier`。
  - `Answer`类存储各类查询指令的答案，保证重复指令只查询一次，节省CPU时间与程序运行时间。



其类图如下：

![1561342709694](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1561342709694.png)





### 1.2 UML2

本次作业在上次作业的基础上，进一步实现了对UML顺序图和UML状态图的解析，以及增加了**三个规则验证**。



#### 分析

##### UMLClassModel

同上次UmlInteraction。



##### UmlCollaboration

collaboration下可以有多个时序图交互

- **第一层次**
  - UmlAttribute（协作对象）
      - _parent：所在的collaboration 我猜(与UmlInteraction相同)
      - type：""   我懵逼了
      扮演Role1,Role2, ... 角色

  - UmlInteraction（交互模型）
      - _parent：所在的collaboration 我猜

- **第二层次**
  - UmlMessage
      - messageSort：消息类型（同步，简单等）
      - _parent：所在的interaction
      - source：消息发出者(lifeline)
      - target：消息接受者(lifeline)
  - UmlLifeline
      - _parent：所在的**interaction**
      - isMultiInstance：不懂
      - represent：所代表的Role（UmlAttribute） 

  - UmlCombineFragment



##### UmlStateChart

- **顶层**
  - UmlStateMachine
      - _parent：上一级

- **第一层**
  - UmlRegion
      - _parent：所在的状态机（UmlStateMachine）

- **第二层**
  - UMLPseudostate(初始状态)
      - _parent：所在Region
  - UmlState
      - _parent：所在Region
  - UMLFinalState
      - _parent：所在Region

- **第三层**
  - UmlTransition
      - _parent：所在Region
      - guard：表示该状态转换所能发生的时机(01阈值)
      - source：源状态
      - target：目的状态

  - UMLEvent
      - _parent：对应所在的transition

  - UmlOpaqueBehavior



#### 架构设计

​	本次设计延用了上次的架构，仍然主要包含两个包：`utils` 和 `elements`。`elements` 补充了`state`以及`interact`等包，分别用于对**状态图与顺序图的解析**，文件树 如下：

```
└─homework
    └─uml2
        │  Main.java
        │
        ├─elements
        │  │  MyUmlElement.java
        │  │
        │  ├─classifier
        │  │      Answer.java
        │  │      MyUmlClass.java
        │  │      MyUmlClassifier.java
        │  │      MyUmlInterface.java
        │  │
        │  ├─interact
        │  │      MyUmlInteraction.java
        │  │      MyUmlStateMachine.java
        │  │
        │  ├─meta
        │  │      MyUmlAssociationEnd.java
        │  │      MyUmlAttribute.java
        │  │      MyUmlLifeline.java
        │  │      MyUmlMessage.java
        │  │      MyUmlOperation.java
        │  │      MyUmlParameter.java
        │  │      MyUmlTransition.java
        │  │
        │  └─state
        │          MyUmlFinalState.java
        │          MyUmlPseudostate.java
        │          MyUmlState.java
        │
        └─utils
                MyUmlClassModelInteraction.java
                MyUmlCollaborationInteraction.java
                MyUmlGeneralInteraction.java
                MyUmlStandardPreCheck.java
                MyUmlStateChartInteraction.java
                
```



#### 类设计

​	本次基于上次作业的架构重点实现了**三个交互类，一个检查类**，并将其耦合在一个`MyUmlGeneralInteraction` 中；同时基于需要，添加了几个相关的`UmlElement`类，并适当修改了`MyUmlClass` 以及`MyUmlInterface`类。

其类图如下：

![1561343522047](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1561343522047.png)





## 2. 四个单元中的架构设计及OO方法理解的演进

#### 第一单元 - 多项式求导

​	一开始，刚刚接触OO的我对于老师与助教不断强调的"架构"的理解懵懵懂懂，而程序设计与分析则更是停留在**C语言面向过程**的编程思维中。本单元作为一个供我们快速入门OO的基础篇，对于作业需求的逐层递进，我认为非常合理且十分有必要的，迫使我们在变幻莫测的需求与测试的夹缝之中，一步步朝着**面向对象**思维的转变。尤其是在第三次作业时新增的对**嵌套函数**的求导，可以说如果没有一个好的架构，是支撑不起这样复杂的**Wrong Format**的判断以及**递归嵌套的求解**的。

​	在本单元的作业中，我在第三次作业中第一次尝试使用了**抽象类**，这样做的好处是对于每个项的求导，我不再需要一个巨大的`switch`来判断其到底是一类，从而进行强制类型转换后再调用相应的求导方法；取而代之的是，对每个`abstract`类的元素，对其方法的调用，会自动向下转型为**对相应子类方法的调用。**	



#### 第二单元——多电梯调度

​	本单元第一次接触多线程，一路走来可以说是十分享(tong)受(ku)了，但多亏了老师在PPT中给我们提供的两种**架构设计思路**，减轻了我们的负担，同时也更好地帮助我们体会架构的重要性与优越性。

​	本单元最终架构还算说得过去，我对电梯的解析主要采用了 **Producer-Consumer** 与 **Guarded Suspension** 模式。主要有**请求输入装置、主控制器以及电梯**三个线程，难点在于对**换乘请求的处理**。但对于**高内聚，低耦合**的把控却不够，尤其是对C电梯的处理。由于迷之3楼只有C电梯能够上去，出于时间紧迫，我最终选择了枚举的方式，考虑了各种可能的情况，如"低楼层->3"、"高楼层->3"、"2->3"、"4->3"等等，大段的`if-else`嵌套，即便有**充分的注释**，回头再看时**理解与检查**起来也十分的**费劲**。



#### 第三单元——类地铁管理系统

​	老实说，本单元最后一次作业一开始的架构十分的差劲，出于种种原因，在ddl前一天晚上选择了重构，结果写了一堆*，强测结果可想而知。在后续bug修复过程中，尝试了**"1+2"、"1+1"式拆点法**以及各种可能的架构，总共重构了四次，每一次重构都有新的体会与感悟，一个优美的架构好处不仅仅在于其可扩展性，由于模块与模块之间耦合度低，逻辑重合度低，其bug调试及定位难度也大幅降低，同时也能更好的借助JUnit进行覆盖性测试。



#### 第四单元——UML元素解析器

​	作为OO课程的最后一个单元，在阅读与学习了整整一个学期优秀的代码后，加上有充分的时间设计，本单元作业的最终架构还算比较满意，并且对可扩展性、耦合度、鲁棒性都有一定的考量，也算小有所成吧。尤其是从第一次到第二次作业的扩展，仅仅是在原有的基础上添加新的功能，而原有架构与功能也经历了**强测的检验**，从而在完成作业时也十分得心应手，更是让我体会到了好的架构的方便之处。



## 3. 测试理解与实践的演进

​	测试是软件工程中必不可少且可以说是最为重要的一个环节，**一个良好的架构是对定点测试与bug修复的前提，对拍器是对大大提升测试效率的工具，而大量随机数据的投喂则是对软件质量的保障。**

​	第一单元难点在于对各种**WF**情况的考虑。在一开始，无论是公测还是互测，我均是在肉眼debug，但主要还是集中在对WF的检测上。在第三次作业中借助python中的numpy模块以及大佬的数据生成器，终于实现了对拍，提高了测试效率，但由此也导致了一个**问题**：我不愿意再去花大量的时间与精力去琢磨对方的程序逻辑，而把希望全部寄托在大量的随机数据上。

​	第二单元则主要是**线程安全**以及**电梯运行时间**的把控。多线程的测试应该是最为头疼的了，虽然官方给提供了标准运行时间的解析包，使得**TLE**问题较为容易进行调控。但线程运行时的随机性而导致的**线程安全问题**，却大大增加了bug定位与复现的难度，从而导致难以调试，因而bug定位更多地仍然是从分析整个程序运行的逻辑上入手。

​	第三单元开始接触到 **JUnit** 单元测试，同时也学习到了基于JML的规格检查以及 JML Unit 工具的使用。此外，输出格式的固定与统一也使得正确性的检验较为容易，直接`fc`即可，给自动化测试的部署带来了极大的便利。

​	第四单元由于数据是基于StarUML的，因而难以生成大量随机数据进行测试，但其对于 **JUnit** 单元测试仍旧十分友好，在本单元的测试中，我仍旧重点采用程序逻辑分析法，对每条**查询指令**以及每一类**规则检查**都尽可能地进行了覆盖性检查，如下是我对`R003`的分析：

```java
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
```



​	**"测试只是为了尽可能地发现bug，而通过测试并不意味着你的程序就没有bug了"。**吴际老师的这句话值得我们去好好反省与深思，我们总是因为过了中测而沾沾自喜，而当强测结果出来时才懊悔不已，痛恨自己如果当初好好做一下测试就好了。可是现实没有如果，假若把这些低级错误，这种侥幸心理放在未来的工作中，很可能迎接你只有一句**"YOU ARE FIRED"**。



## 4. 课程收获

​	一学期的OO之旅终于到了终点，这期间踩了不少坑，也吃了不少苦头，但从零基础一路走来，真的能感受到自己的巨大进步。在第一单元，我学会了正则表达式的使用以及OO的基本思想如类，接口，继承等；第二单元则学会了多线程程序的设计，包括线程安全的人为把控，以及SOLID设计原则等；第三单元学习java的建模语言，意识到了设计与实现分离的重要性以及必要性，同时初步体会到了网络流+拆点的精妙之处；最后一个单元的练习更像是一个总结，不仅是对更**广义上的面向对象**建模设计UML模型的理解，还是对前几个单元所有学习到的知识的一个汇总，整理以及实际运用，都令我受益匪浅。此外，老师及助教也不断强调要严格遵循代码规范，培养良好的编码风格，不能每次都依靠CheckStyle信息去调整，经过一个学期的磨炼，我的codestyle也有了很大的改进与提升。

​	总之，一学期下来，确实能感受到自己己的能力在稳步提升，也逐渐从面向过程的思维中转变了过来，但距离一个优秀的架构师仍有很大距离，我仍然需要大量及深入地通过阅读专业书籍以及模范代码，学习更多更巧妙的设计思想，逐渐形成一套自己的思维体系。 



## 5. 一点建议

1. 我认为可以适当减少互测屋的人数，在OO与OS两座大山前，我们很难有足够的精力去把同屋其他7个人的代码都认真研读一遍，更不用说体会其中的精妙，同时找出逻辑bug了。我想，大部分人都会选择部署自动化工具，进行随机测试，如果没有跑出bug，那就随缘...
2. Bug修复阶段，对于非合并修复驳回的说明过于简略，且过于晚... 希望不要让认真修bug的同学心凉...
3. 关于Bug修复的接口可以一直保留，便于我们回看并总结自己的bug。
4. 关于网站，希望可以有侧边的滑动栏... 不然每次都要滚轮滚好久好久...



最后，在此衷心感谢OO课程组的老师及助教们，你们辛苦了，真心祝愿OO课程越来越好！









































