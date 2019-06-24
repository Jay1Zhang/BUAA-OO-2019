package oocourse.elevator3.data;

import com.oocourse.elevator3.PersonRequest;

import java.util.ArrayList;

import static oocourse.elevator3.data.Config.dockableFloorsOfA;
import static oocourse.elevator3.data.Config.dockableFloorsOfB;
import static oocourse.elevator3.data.Config.dockableFloorsOfC;
import static oocourse.elevator3.data.Config.Status;
import static oocourse.elevator3.data.Config.EleId;

/**
 * 重新封装了Request,用于处理拆分请求
 * 保证只有main请求对外可见
 */
public class Request {
    private PersonRequest mainRequest;
    private PersonRequest childRequest;
    private ArrayList<EleId> mainOptEleList = new ArrayList<EleId>();
    private ArrayList<EleId> childOptEleList = new ArrayList<EleId>();

    public Request(PersonRequest personRequest) {
        int fromFloor = personRequest.getFromFloor();
        int toFloor = personRequest.getToFloor();
        int personId = personRequest.getPersonId();
        boolean nonstop = false;
        // 若为可以直达的请求, 找出其可乘坐的电梯
        if (dockableFloorsOfA.contains(fromFloor)
                && dockableFloorsOfA.contains(toFloor)) {
            nonstop = true;
            mainOptEleList.add(EleId.A);
        }

        if (dockableFloorsOfB.contains(fromFloor)
                && dockableFloorsOfB.contains(toFloor)) {
            nonstop = true;
            mainOptEleList.add(EleId.B);
        }

        if (dockableFloorsOfC.contains(fromFloor)
                && dockableFloorsOfC.contains(toFloor)) {
            nonstop = true;
            mainOptEleList.add(EleId.C);
        }

        if (nonstop) {
            mainRequest = new PersonRequest(fromFloor, toFloor, personId);
            childRequest = null;
        } else {
            // 拆分请求
            resolveRequest(fromFloor, toFloor, personId);
        }

    }

    /**
     * 在不考虑当前电梯状态的情况下
     * 仅凭出发与目的楼层，解析出拆分请求的最优解
     * 优先级为 A->B->C
     * @param fromFloor
     * @param toFloor
     * @param personId
     */
    private void resolveRequest(int fromFloor, int toFloor, int personId) {
        int mainFromFloor = fromFloor;
        int mainToFloor = 1;
        int childFromFloor = 1;
        int childToFloor = toFloor;

        if (dockableFloorsOfA.contains(fromFloor)) {
            mainOptEleList.add(EleId.A);
            // fromFloor 必然在 -3-1, 15-20
            // toFloor 必然在 2-14层之间
            if (toFloor == 3) {
                // 只有C电梯可以到达
                childOptEleList.add(EleId.C);
                // 故可以让电梯A把人送到 1、15层
                if (fromFloor < 3) {
                    // 既然您在楼下，那您就先去1楼吧
                    mainToFloor = childFromFloor = 1;
                    //childFromFloor =  1;
                } else {
                    // 既然您在楼上，那您就先去15楼吧
                    mainToFloor = childFromFloor = 15;
                    //childFromFloor = 15;
                }
            } else {
                // 既然B电梯可达，那为何不乘坐B呢？又大又快
                childOptEleList.add(EleId.B);
                if (fromFloor < 2) {
                    // 既然您在楼下，那您就先去1楼吧
                    mainToFloor = childFromFloor = 1;
                    //childFromFloor =  1;
                } else if (fromFloor > 14) {
                    // 既然您在楼上，那您就先去15楼吧
                    mainToFloor = childFromFloor = 15;
                    //childFromFloor = 15;
                }
            }
        } else if (dockableFloorsOfB.contains(fromFloor)) {
            mainOptEleList.add(EleId.B);
            // fromFloor 必然在 -2-2, 4-15
            // toFloor 必然在 -3,3,16-20层之间
            if (toFloor == 3) {
                // 只有C电梯可以到达
                childOptEleList.add(EleId.C);
                // 故可以让电梯B把人先送到 1、5层
                if (fromFloor < 3) {
                    // 既然您在楼下，那您就先去1楼吧
                    mainToFloor = childFromFloor = 1;
                    //childFromFloor =  1;
                } else {
                    // 既然您在楼上，那您就先去5楼吧
                    mainToFloor = childFromFloor = 5;
                    //childFromFloor = 5;
                }
            } else {
                // 不在3层？那您没得选，只能坐A了
                childOptEleList.add(EleId.A);
                // toFloor 必为 -3，16-20
                if (toFloor == -3) {
                    // 算了，也别A优先了，您直接坐到-2楼吧
                    mainToFloor = childFromFloor = -2;
                    //childFromFloor = -2;
                } else {
                    // 既然您要上到16-20楼，那就先去15楼吧
                    mainToFloor = childFromFloor = 15;
                    //childFromFloor = 15;
                }
            }
        } else {
            // 能走到这？fromFloor 必然为 3
            mainOptEleList.add(EleId.C);
            // toFloor 为 -3，-2，-1，{ 2，4,6,8,10,12,14 }，16-20
            // 若toFloor在中括号内，则乘坐B；否则，乘坐A
            if (toFloor < 2) {
                childOptEleList.add(EleId.A);
                // 看来您要去-3，-2，-1楼，那先下到1楼吧
                mainToFloor = childFromFloor = 1;
                //childFromFloor = 1;
            } else if (toFloor > 14) {
                childOptEleList.add(EleId.A);
                // 看来您要上到16-20楼，那先上到15楼吧
                mainToFloor = childFromFloor = 15;
                //childFromFloor = 15;
            } else {
                childOptEleList.add(EleId.B);
                // 看来您还没下班，要在{}办公层接着工作呢！坐B吧！
                if (toFloor == 2) {
                    // 3 -> 2，您只能 3->1,1->2
                    mainToFloor = childFromFloor = 1;
                    //childFromFloor = 1;
                } else {
                    // 先上5楼吧，然后换乘B
                    //childFromFloor = 5;
                    mainToFloor = childFromFloor = 5;   }

            }
        }

        this.mainRequest = new PersonRequest(
                mainFromFloor, mainToFloor, personId);
        this.childRequest = new PersonRequest(
                childFromFloor, childToFloor, personId);
    }

    public boolean contains(EleId id) {
        if (mainOptEleList.contains(id)) {
            return true;
        } else {
            return false;
        }
    }

    public boolean hasChildRqst() {
        if (childRequest == null) {
            return false;
        } else {
            return true;
        }
    }

    public void changeMainRqst() {
        this.mainRequest = this.childRequest;
        this.childRequest = null;
        this.mainOptEleList = this.childOptEleList;
        this.childOptEleList = null;
    }

    public Status getStatus() {
        if (mainRequest.getFromFloor() < mainRequest.getToFloor()) {
            return Status.UP;
        } else {
            return Status.DOWN;
        }
    }

    public int getFromFloor() {
        return mainRequest.getFromFloor();
    }

    public int getToFloor() {
        return mainRequest.getToFloor();
    }

    public int getPersonId() {
        return mainRequest.getPersonId();
    }

    public String toString() {
        return String.format("%d-FROM-%d-TO-%d", mainRequest.getPersonId(),
                mainRequest.getFromFloor(), mainRequest.getToFloor());
    }

    public String getOptEleStr() {
        return mainOptEleList.toString();
    }

    public ArrayList<EleId> getOptEleList() {
        return mainOptEleList;
    }
}
