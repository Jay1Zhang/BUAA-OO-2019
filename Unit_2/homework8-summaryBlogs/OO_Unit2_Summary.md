# OO第二单元总结

### 0. 前言

> 作为程序员，今天你决定翘掉晚上的加班，约女朋友看电影。
>
> 电影是 20:00 开始。
>
> 虽然翘掉了加班，但你从公司出来，就已经 19:00 了。
>
> 公司在望京 SOHO，约会地点在朝阳大悦城。
>
> （这点时间，祝你好运吧）
>
> 也许你运气真的很好，19:50 就赶到商场了。
>
> 心里想：“还有10分钟才开始，电影院在 F8，乘个直梯，两分钟就到，今天真美好。”
>
> 你按了上行按钮，并行的 3 部电梯，一部正从 F2 升 F3，一部刚刚打算从 F8 降下来，另一部刚降到 F3 竟然又升上去了！
>
> （理论上讲，一部电梯，如果从 F8 以自由落体的方式下来，不超过 3s；如果正常运行下来，大概 105s；）
>
> 可是......
>
> 你到达电影院时，已经 20:10 了
>
> 你的女朋友也等得不耐烦了......
>
> ​																		摘自 《[我猜，每个程序员对着电梯都想过调度算法吧！](<https://blog.csdn.net/gitchat/article/details/80202416>)》



### 1. 第五次作业（傻瓜电梯）

#### 1.1 架构设计

第一次是真真正正的傻瓜电梯，没有进行任何的优化处理。

#### 类设计

- 数据类
  - `PersonRequest` 请求类，存放请求信息（已知）
  - `RequestQueue`类，存放请求队列——**sharedResource**
- 线程类
  - `RequestInputDevice`类，请求输入装置——类似**inputDemo**
  - `Elevator`类，接收并处理请求，输出——类似**outputDemo**
- 入口类
  - `Main`

类图如下：

![1555981882638](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555981882638.png)



#### 多线程设计

- 设计模式：采用 Producer-Consumer 及 Guarded Suspension 模式
- 共享对象：由 `Elevator` 和 `RequestInputDevice` 共享一个请求队列
- 线程安全：在 `RequestQueue` 中利用实现了 `LinkedList` 接口的 `Queue` 对象来存储 `PersonRequest`，并将 `getRequest()` 与 `putRequest()` 加了 `synchronized` 锁以确保线程安全。

UML协作图如下：

![1555985801687](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555985801687.png)



#### 1.2 基于度量分析

利用 **Metrics** 工具分析结果如下：

![1555986232466](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555986232466.png)

![1555986343462](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555986343462.png)



#### 分析

由于第一次作业较为简单，整体来看，方法及类复杂度均比较小，**唯独 `Elevator` 鹤立鸡群**。经查，发现是因为我将请求调度与电梯的运行逻辑均融在了电梯类中，使得 `Elevator` 有点 `God class` 的意思。且由于第一次作业采用**傻瓜调度模式**，根据请求的出发楼层与目的楼层计算出电梯运行的时间，导致 `resolveRequest` 方法中嵌套了大量的 `if-else` 语句，导致了模块复杂度较高。



#### SOLID原则分析

- `Single Responsibility Principle`：`Elevator` 类职责不明确。电梯本应该只负责根据请求信息运行完成接送人的工作即可，解析请求以及根据请求进行调度本就不是电梯应该“操心”的事。
- `Open Close Principle`：同上SRP原则，我在设计之初没有意识到这个问题，导致电梯类内部逻辑难以封闭。在第二次作业更改调度策略时，该这种设计的劣势便显露无疑。
- `Lisov Substitution Principle`：未使用继承
- `Interface Segregation Principle`：未使用接口
- `Dependency Inversion Principle`：未使用抽象类



#### 自我点评

- 优点：
  - 采用 `Producer-Consumer` 的设计模式，架构十分简洁清晰。
  - 结合 `Guarded Suspension` ，保证线程安全的同时，与架构完美契合。
- 缺点：
  - 电梯与调度器融为一体，没有做到**低耦合**的设计原则，可扩展性差。



#### 1.3 Bug分析

本次作业公测与互测均未出现bug，也并未测出对方bug。



### 2. 第六次作业（ALS可捎带电梯）

#### 2.1 架构设计

第二次电梯作业在分析了很久的指导书后，发现无论是哪种调度策略都会出现性能大大弱于ALS策略的特例情况，为了保证不被卡**Tmax**，最终采用了严格按照指导书的ALS调度策略。只对下面一种情况在主请求的选择上作了优化：

- [0.0]1-FROM-10-TO-3
- [0.1]2-FROM-5-TO-15

当电梯运行到五层时，电梯中还没有乘客，1号乘客的请求作为主请求。 此时电梯主请求的目标楼层（3层）与被捎带请求的目标楼层（15层），两者在当前楼层（5层）的**异侧**。 但是电梯运行方向（UP）与该请求（FROM-5-TO-15）的目标方向（UP）却是**一致的**。按照指导书的ALS规则，主请求显然是不更换的，而如果捎带2号乘客且更换主请求，电梯运行方式变为1-15-3，比原本的运行时间短。



#### 类设计

- 数据类

  - `PersonRequest` 请求类，存放请求信息（已知）

  - `Constant` 常量类，存放常量。

  - `RequestQueue`类，存放请求队列——shared by RequestInputDevice & Elevator

  - - `InputEnd()`方法：当队列为空且endTag为真时，返回true

  - `PiggybackQueue`类，捎带队列——shared by Dispatcher & Elevator

  - - **伪实时更新 —— 电梯每ARRIVE一层，开关门期间**
    - 由调度器解析请求队列，并将符合捎带规则的请求放入捎带队列
    - 由电梯解析捎带队列，并将其加入乘客队列
    - **需要执行的操作是：到达指定楼层FromFloor - IN**

  - `Passengers`类，乘客队列——电梯内部私有属性

  - - 由电梯自己进行维护
    - **需要执行的操作是：到达指定楼层toFloor - OUT**

- 线程类

  - `RequestInputDevice`类，请求输入装置——生产者

  - - 监视控制台输入，若有请求进入，则加入请求队列
    - 若读完了所有请求，设置requestQueue 输入结束状态为真，并结束该输入线程。

  - `Dispatch`类，中央调度器——采取单例模式

  - - // 可能需要不断地扫描请求队列以及不断轮询电梯的状态

    - 当电梯处于WAIT状态时，

    - - get请求队列中到达时间最早（即队首）的请求，并发送给Elevator

    - 当电梯处于MOVE状态时，

    - - 不断更新电梯的当前楼层及状态，

      - - 若请求队列中有当前楼层的请求，且该请求的状态与电梯状态相同（即运行方向相同），则加入捎带队列

    - 当**电梯处于WAIT状态 & 请求队列为空 & 输入为null** 时， 终止电梯线程

    - - 输入为null则set请求队列的endTag为真

  - `Elevator`类，输出——消费者

  - - 电梯的状态

    - - 电梯输出状态共有三种：{ ARRIVE, OPEN, CLOSE }
      - 运动状态共有三种：{ WAIT，UP，DOWN }

    - 当电梯处于WAIT状态时，等待被调度器唤醒

    - - 调度器抓取requestQueue的请求并根据**一定策略**发送给Elevator

    - 当电梯处于UP/DOWN状态，即MOVE状态时，

    - - 每ARRIVE一层就查询一次piggybackQueue（捎带队列），如果有**符合条件的请求**，则捎带

      - - 至于什么才是符合条件的请求，不是电梯该考虑的问题，全权交给调度器去判断

      - 当捎带队列的请求执行完毕时，则向调度器索要**主请求**，并继续MOVE；若无主请求，则进入WAIT状态。

      - - 将捎带队列队首的请求作为主请求

- 入口类

  - Main

类图如下：

![1555988633675](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555988633675.png)

#### 多线程设计

- 设计模式：仍旧采用 Producer-Consumer 模式，只是作了进一步的拓展。
- 共享对象：由 `Dispatcher` 和 `RequestInputDevice` 共享一个请求队列，由`Dispatcher `和 `Elevator` 共享一个捎带队列。
- 线程安全：为了遍历方便，将所有存放请求的数据结构改为了较为熟悉的 `ArrayList` 来存放。为了保证线程安全，将各个队列的 `getRequest()` 与 `putRequest()` 加了 `synchronized` 锁以确保线程安全。

UML时序图如下：

![1555990244918](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555990244918.png)



#### 2.2 基于度量分析

利用 **Metrics** 工具分析结果如下：

![1555990300771](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555990300771.png)

![1555990354036](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555990354036.png)



#### 分析

由上可见，本次模块复杂度与类复杂度并不乐观，问题主要仍出在 `Elevator` 与 `Dispatcher` 中。经查，由于逻辑设计混乱，为保证能够正确捎带，在电梯的 `run()` 方法中多次调用 `updatePiggybackQueue` 与 `updateMainRequest` 方法，导致该方法基本复杂度较高，使这段程序难以理解，难以模块化和维护。



#### SOLID原则分析

- `Single Responsibility Principle`：`RequestInputDevice`负责读入请求，`Dispatcher` 根据请求队列与电梯状态，“实时”更新可捎带队列，`Elevator` 则根据自身内部的乘客队列以及各楼层的可捎带队列工作并接送人。整体来看比较符合类功能的独立性。
- `Open Close Principle`：相较第一次作业，本次架构向多电梯扩展相对容易一些（但由于电梯内部run方法的复杂逻辑，以及新增的对电梯可停靠楼层以及载客量、速度等的限制，最终还是选择了重写该类）
- `Lisov Substitution Principle`：未使用继承
- `Interface Segregation Principle`：未使用接口
- `Dependency Inversion Principle`：未使用抽象类



#### 自我点评

- 优点
  - 实现了请求队列与调度器分离，可扩展性好。
- 缺点
  - 电梯内部逻辑混乱，写的不优美



#### 2.3 Bug分析

##### 我方

本次公测与互测均未被发现bug。

##### 对方

在经过仔细研究对方 `Elevator` 类中的 `run` 方法后发现，其接送人逻辑为：

- OPEN
- sleep(200)
- output "IN & OUT"
- sleep(200)
- CLOSE

而其乘客队列的更新确是实时进行的，因而我构造了这样的一组数据

- [0.0]1-FROM-1-TO-15
- [0.3]2-FROM-1-TO-15

运行结果如下：

![1555992091174](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555992091174.png)

可以看到，在1楼时，2号乘客并没有进入电梯，而在15楼却莫名奇妙的出现了？

虽然已确定bug，但在上交测试样例时足足交了4次才hack到这个点，至今仍十分不解...



### 3. 第七次作业（多电梯调度）

#### 3.1 架构设计

本次作业在研究完指导书后发现最令人头疼的便是换乘请求的处理，在架构上也是设计一版扔一版；而在性能上，考虑到多电梯调度的复杂性以及官方保证了**真·随机数据**，最后还是采用了上次作业的ALS策略的优化版。

#### 类设计

- 数据类

  - 新增Request类
    - 该类重新封装了PersonRequest类，目的是为了便于处理换乘请求。
    - 在构造一个Request对象时，会在类内部判断是否是直达请求，如果必须换乘，则将请求在内部拆分，每次只对外显示一个请求，当第一个请求完成时，在对外显示第二个请求。
    - 考虑到**必须换乘**的情况的特殊性（最主要是迷之3楼），直接采用了暴力拆分大法。
  - 其余同第二次电梯作业

- 线程类

  - 电梯

    - 新增 boolean FULL，判断

    - 新增 各种限制信息，private final，保证初始化后不再更改，比如：

    - - 最大载客量
      - 运行速度
      - 开关门时间

  - 主调度器

    - 不断从请求队列中拿出请求，并根据一定的调度规则将请求加入电梯的停靠队列中。

  - 请求输入装置

    - 同第二次电梯作业

- 入口类

  - Main

类图如下：

![1555993082283](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555993082283.png)



#### 多线程设计

- 设计模式：仍旧采用 Producer-Consumer 模式，只是作了进一步的拓展。
- 共享对象：由 `MainCtrl` 和 `RequestInputDevice` 共享一个请求队列，由`MainCtrl ` 分别和三部 `Elevator` 共享三个等待队列。
- 线程安全：同第二次作业，为了遍历方便，将所有存放请求的数据结构改为了较为熟悉的 `ArrayList` 来存放。为了保证线程安全，将各个队列的 `getRequest()` 与 `putRequest()` 加了 `synchronized` 锁以确保线程安全。

UML时序图如下：

![1555993517411](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555993517411.png)



#### 3.2 基于度量分析

利用 **Metrics** 工具分析结果如下：

| Method                                                       | ev(G)  | iv(G)  | v(G)   |
| ------------------------------------------------------------ | ------ | ------ | ------ |
| SelfTestMainClassForTimableOutput.main(String[])             | 1      | 1      | 1      |
| TestInput.main(String[])                                     | 3      | 3      | 3      |
| TestRequest.main(String[])                                   | 1      | 2      | 2      |
| oocourse.elevator3.Main.main(String[])                       | 1      | 1      | 1      |
| oocourse.elevator3.data.Dispatcher.Dispatcher(WaitingQueue,Elevator) | 1      | 1      | 1      |
| oocourse.elevator3.data.Passengers.getFirstRequest()         | 1      | 1      | 1      |
| oocourse.elevator3.data.Passengers.getRequest(int)           | 1      | 1      | 1      |
| oocourse.elevator3.data.Passengers.hasPassenger(int)         | 3      | 2      | 3      |
| oocourse.elevator3.data.Passengers.isEmpty()                 | 1      | 1      | 1      |
| oocourse.elevator3.data.Passengers.nextPassenger(int)        | 3      | 3      | 3      |
| oocourse.elevator3.data.Passengers.putRequest(Request)       | 1      | 1      | 1      |
| oocourse.elevator3.data.Passengers.remove(int)               | 1      | 1      | 1      |
| oocourse.elevator3.data.Passengers.size()                    | 1      | 1      | 1      |
| oocourse.elevator3.data.Request.Request(PersonRequest)       | 1      | 8      | 8      |
| oocourse.elevator3.data.Request.changeMainRqst()             | 1      | 1      | 1      |
| oocourse.elevator3.data.Request.contains(EleId)              | 2      | 1      | 2      |
| oocourse.elevator3.data.Request.getFromFloor()               | 1      | 1      | 1      |
| oocourse.elevator3.data.Request.getOptEleList()              | 1      | 1      | 1      |
| oocourse.elevator3.data.Request.getOptEleStr()               | 1      | 1      | 1      |
| oocourse.elevator3.data.Request.getPersonId()                | 1      | 1      | 1      |
| oocourse.elevator3.data.Request.getStatus()                  | 2      | 1      | 2      |
| oocourse.elevator3.data.Request.getToFloor()                 | 1      | 1      | 1      |
| oocourse.elevator3.data.Request.hasChildRqst()               | 2      | 1      | 2      |
| oocourse.elevator3.data.Request.resolveRequest(int,int,int)  | 1      | 7      | ==13== |
| oocourse.elevator3.data.Request.toString()                   | 1      | 1      | 1      |
| oocourse.elevator3.data.RequestQueue.InputEnd()              | 1      | 1      | 1      |
| oocourse.elevator3.data.RequestQueue.doNotify()              | 1      | 1      | 1      |
| oocourse.elevator3.data.RequestQueue.getRequest()            | 3      | 4      | 5      |
| oocourse.elevator3.data.RequestQueue.isEmpty()               | 1      | 1      | 1      |
| oocourse.elevator3.data.RequestQueue.putRequest(Request)     | 1      | 1      | 1      |
| oocourse.elevator3.data.RequestQueue.setInputEndTag(boolean) | 1      | 1      | 1      |
| oocourse.elevator3.data.WaitingQueue.getFirstRequest()       | 1      | 1      | 1      |
| oocourse.elevator3.data.WaitingQueue.getRequest(int)         | 1      | 1      | 1      |
| oocourse.elevator3.data.WaitingQueue.hasWaitRqst(int,Status,boolean) | ==4==  | 5      | 6      |
| oocourse.elevator3.data.WaitingQueue.isEmpty()               | 1      | 1      | 1      |
| oocourse.elevator3.data.WaitingQueue.isMainCtrlEndTag()      | 1      | 1      | 1      |
| oocourse.elevator3.data.WaitingQueue.nextWaitRqst(int,Status,boolean) | ==4==  | 6      | 6      |
| oocourse.elevator3.data.WaitingQueue.putRequest(Request)     | 1      | 1      | 1      |
| oocourse.elevator3.data.WaitingQueue.remove(int)             | 1      | 1      | 1      |
| oocourse.elevator3.data.WaitingQueue.setMainCtrlEndTag(boolean) | 1      | 1      | 1      |
| oocourse.elevator3.data.WaitingQueue.size()                  | 1      | 1      | 1      |
| oocourse.elevator3.thread.Elevator.Elevator()                | 1      | 1      | 1      |
| oocourse.elevator3.thread.Elevator.getCurrentFloor()         | 1      | 1      | 1      |
| oocourse.elevator3.thread.Elevator.getNumOfPsgers()          | 1      | 1      | 1      |
| oocourse.elevator3.thread.Elevator.getStatus()               | 1      | 1      | 1      |
| oocourse.elevator3.thread.Elevator.isEmpty()                 | 1      | 1      | 1      |
| oocourse.elevator3.thread.Elevator.isFull()                  | 2      | 1      | 2      |
| oocourse.elevator3.thread.Elevator.isStill()                 | 2      | 3      | 4      |
| oocourse.elevator3.thread.Elevator.move()                    | 2      | 5      | 7      |
| oocourse.elevator3.thread.Elevator.run()                     | 3      | 7      | 8      |
| oocourse.elevator3.thread.Elevator.sendPassengers()          | 1      | 3      | 3      |
| oocourse.elevator3.thread.Elevator.takePassengers()          | 1      | 3      | 3      |
| oocourse.elevator3.thread.Elevator.updateStatus()            | 3      | 4      | 5      |
| oocourse.elevator3.thread.MainCtrl.MainCtrl(RequestQueue)    | 1      | 1      | 1      |
| oocourse.elevator3.thread.MainCtrl.dispatchRequest(Request)  | ==11== | ==13== | ==19== |
| oocourse.elevator3.thread.MainCtrl.run()                     | ==4==  | 7      | 8      |
| oocourse.elevator3.thread.RqstInputDevice.RqstInputDevice(RequestQueue) | 1      | 1      | 1      |
| oocourse.elevator3.thread.RqstInputDevice.run()              | 3      | 4      | 4      |

| Class                                     | OCavg | WMC    |
| ----------------------------------------- | ----- | ------ |
| SelfTestMainClassForTimableOutput         | 1     | 1      |
| TestInput                                 | 3     | 3      |
| TestRequest                               | 2     | 2      |
| oocourse.elevator3.Main                   | 1     | 1      |
| oocourse.elevator3.data.Config            | n/a   | 0      |
| oocourse.elevator3.data.Config.EleId      | n/a   | 0      |
| oocourse.elevator3.data.Config.Status     | n/a   | 0      |
| oocourse.elevator3.data.Dispatcher        | 1     | 1      |
| oocourse.elevator3.data.Passengers        | 1.5   | 12     |
| oocourse.elevator3.data.Request           | 2.58  | ==31== |
| oocourse.elevator3.data.RequestQueue      | 1.33  | 8      |
| oocourse.elevator3.data.WaitingQueue      | 1.6   | 16     |
| oocourse.elevator3.thread.Elevator        | 2.42  | 29     |
| oocourse.elevator3.thread.MainCtrl        | ==8== | 24     |
| oocourse.elevator3.thread.RqstInputDevice | 2     | 4      |

#### 分析

可以看出，即便是经过深思熟虑才设计出来的架构，仍然存在不小的问题。但这一次问题主要集中在 `MainCtrl` 以及新增的 `Request` 类。我在构造 `Request` 对象时，由于采用了暴力拆分的解析方法，枚举了所有可能的换乘情况而不考虑电梯的状态，并从中选出最优策略进行调度，导致在 `resolveRequest()` 方法中嵌套了大量大量的 `if-else` 语句，足足有60行（刚好卡着Code Style的线···）。而 `MainCtrl` 中对电梯的调度策略仍然是一个不小的难题，也同样不出所料的导致模块复杂度较高。



#### SOLID原则分析

- `Single Responsibility Principle`：由于是在第二次作业的基础上扩展而来，整体还算比较符合类功能的独立性。
- `Open Close Principle`：不得不说，`Request` 类**完全不符合**开闭原则的设计。哪怕电梯系统有一星半点的扩展，都要重写 `resolveRequest()` 方法，毫无扩展性可言。相比之下，电梯类的设计就比较优美，能够接受多部电梯的扩展。
- `Lisov Substitution Principle`：未使用继承。但实际上，由于我用到的三个队列均需要不断的 `putRequest` 以及 `getRequest`，因而 `waitingQueue` 以及 `Passengers` 两个队列是可以设计为`RequestQueue`  的子类，使得架构更加的优美。
- `Interface Segregation Principle`：同上，三个队列可以同样实现一个请求队列的接口，保证架构的同时不失扩展性。
- `Dependency Inversion Principle`：未使用抽象类



#### 自我点评

- 优点
  - Request 类的设计十分巧妙，每次对外只显示一个类，而不需要在额外维护一个队列，增加开销。
  - 三个队列的设计使得模块间耦合程度较低，可扩展性强
- 缺点
  - 同样是由于三个队列的设计，虽然保证了模块的独立性，但给进一步优化带来的不小的麻烦。比如只是想让三部电梯随机抢人都会出现各种各样的线程安全错误。



#### 3.3 Bug分析

##### 我方

本次作业···被发现了一个重大的bug，该bug甚至差点导致无效作业，（虽然已经和无效作业差不多了）。在电梯开门接送人的过程中，应当遵循**先下后上**的原则，而我忽略了这个微小的细节，照搬第二次作业的设计（第二次电梯作业并无载客量的限制）先 `IN` 后 `OUT` ，同时由于调度规则的限制，虽然没有超载，但却导致了更加致命错误——电梯会上到21层或下到-4层。因为这一个bug···，强测挂了14个点，互测也被炸翻了天，而实际上，我只需更改一行代码，即将 `takePassenger` 与 `sendPassenger` 的执行顺序调换一下即可··· 真的是欲哭无泪···

##### 对方

本次作业在经过大量随机样例的测试下，发现了对方的bug，在某些需要换乘的随机样例中，会出现下面这种情况

![1555995299378](C:\Users\94831\AppData\Roaming\Typora\typora-user-images\1555995299378.png)

但遗憾的是，此类线程安全的问题难以复现，在上交了多次样例无果后，选择了放弃···



### 4. 心得体会

​	三周的多线程之旅已然结束，这期间当然又踩了很多坑，也吃了不少经验教训。

​	首先，线程安全是最令人头疼的一件事，无脑的加锁不仅会破坏原有架构，更重要的是很可能有逻辑漏洞，导致死锁或者出现其他一些令人意想不到的结果。

​	其次，在设计模式上，在一开始的架构设计中，并没有过多的依照SOLID原则进行思考，最后也正如助教所言**”重构一时爽，但并非一直重构一直爽，很有可能一次重构就火葬场了“**。一个好的设计模式，一个好的架构，一定是兼具正确性与扩展性的，而目前我仅仅处于多线程的初级阶段，应该充分利用经过前辈们精雕细刻打磨出来的设计模式，而不要过于自信，设计一个自己都想不明白到底属于哪一类的架构。比如第三次作业，就出现了电梯越界的情况，如果架构设计的不好，很容易在细节上有所疏漏，导致灾难性的后果发生。

​	最后，对于性能的优化上，在hdl开的《事后孔明》一贴中，了解到了dl评估调度算法优劣的方法，着实令我大开眼界。如助教所言，“**电梯可以增加一个功能，那就是记录下自己的总运行数据（里程，请求数，时间等），然后调度器根据三个电梯的相关数据进行整体优化，向相对空闲的电梯倾斜**”。通过对这些数据指标进行评估，快速定位可能的性能瓶颈，而不用花费大量时间对所有运行结果进行逐一分析（是我没错了······）。但同样如助教所说的“**想要实现这一点，则必须在架构上充分下足功夫才有可能**”。

​	呜呼哀哉，故非人皆hdl，吾及dl之路，远矣。









































