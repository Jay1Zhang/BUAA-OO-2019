# Readme

这是OO的最后一个UML项目作业。



### 遗留问题

- ~~三种规则再审查~~
  - ~~R001~~
  - ~~R002~~
  - ~~R003~~
    - 自己继承自己？

- ~~是否需要考虑类的多继承~~
  - 好像不用考虑
- ~~在R001的检查中，如果类名重复怎么办？~~
  - 如果会出现这种情况的话，这种写法就有问题了
- ~~在R002中，指导书提到**要考虑类和接口之间的实现关系**，这种关系哪种情况下会形成自环？~~
  - 不需要考虑
- ~~初始状态和结束状态可以有名字吗，如果可以，在后继状态时是否会查询到？(重点！！！)~~
  - 规定了，均为null，且不会有查询
  - 而且**规定了初始状态不能有incoming，末状态不能有outgoing迁移**
- ~~初始状态和结束状态均分别看作一个状态吗？在求状态数和后继状态时也只考虑一次嘛？(重点！！！)~~
  - 约束了，初始状态和结束状态均最多只有一个
- ~~有关UMLInteraction的参与对象，在统计incoming时使用了lifelinename，而在计数的时候应该使用同fatherId的attribute（来自吴老师），是否存在疑惑点？~~
  - 我目前是只统计lifeline的数量
  - 确保了，每个顺序图中，Lifeline和其Represent均一一对应。



### COMMIT LOG

#### init

- 初始化，大致完成了整体架构



#### except R003 and getReachableStateId()

- 完成了大体功能

- 除了重复继承，

- 求后继状态的逻辑有点问题



#### fixed bug of getSubsequentStateCount()

- 修复了求解后继状态的bug
  - 不能直接算自己



#### fixed bug in R001

- 伪修复
  - 检查每个assoc的名字时忘记打标记了
  - 但主要不是这个bug···



#### finished R003

- 完成了重复继承的求解



#### fixed bug2 in R001

- 修复了有关AssociationEnd 的名字问题
  - 之前误以为end的名字就是相应的类或接口，在`MyUmlAssociationEnd` 重写了 `getName()` 方法，导致名称有误，抛出的异常有问题
  - 保证 `getName()` 调用其父类 `MyUmlElement` 的方法，即得到自己的名字即可。



#### fixed bug in R003

忘了···



#### fixed bug in R002 and add README.md

- 修复了R002的bug
  - 当出现形如 6 的继承链时，环外部的类是不需要输出的
  - 注意6可能有两种情况
    - 链是叶子子类
    - 链是顶级父类

- 增加了README说明



#### fixed bug in R003 about C1 implement I1, I2 && I2 extends I1

- 修复内容如下，但尚未考虑 **自继承**，实际上，自继承应该归为 **R002，即循环继承**

```Java
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



#### fixed bug about self-inheritance of umlclass

- 修复了 类自继承的bug
  - 此时应为循环继承。



#### fixed bug in R001 about dup-attr in class

- 修复了 类内部重复属性的bug
  - 与上次不同，由于本次作业加入了R001规则，所以指导书鬼畜的指明，可能会出现重复属性的数据