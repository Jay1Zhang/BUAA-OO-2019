package util;

import com.oocourse.specs3.models.NodeIdNotFoundException;
import com.oocourse.specs3.models.NodeNotConnectedException;
import com.oocourse.specs3.models.Path;
import com.oocourse.specs3.models.PathNotFoundException;
import com.oocourse.specs3.models.RailwaySystem;
import base.Node;
import factory.RailwayGraphFactory;
import factory.UnpleasantGraphFactory;
import java.util.HashMap;

public class MyRailwaySystem extends MyGraph implements RailwaySystem {
    /*   Abstract Graph  */
    // <NodeId, stNode>     : pathId = 0
    private HashMap<Integer, Node> stMap = new HashMap<>();
    private HashMap<Node, Integer> stNodes = new HashMap<>();

    /*   weight matrix  */
    private RailwayGraphFactory transferMatrix;
    private RailwayGraphFactory priceMatrix;
    private UnpleasantGraphFactory unpleasantMatrix;

    public MyRailwaySystem() {
        this.transferMatrix = new RailwayGraphFactory(0, 1);
        this.priceMatrix = new RailwayGraphFactory(1, 2);
        this.unpleasantMatrix = new UnpleasantGraphFactory();
    }

    /* 地铁网络的构建 */
    private void addEdge2adjList(Node fromNode, Node toNode, int edgeType) {
        transferMatrix.addEdge2adjList(fromNode, toNode, edgeType);
        priceMatrix.addEdge2adjList(fromNode, toNode, edgeType);
        unpleasantMatrix.addEdge2adjList(fromNode, toNode, edgeType);
    }

    private void addNode2Map(Integer nodeId, Integer pathId) {
        if (!stMap.containsKey(nodeId)) {
            // 若第一次加入该结点, 拆点并更新stMap
            Node stNode = new Node(nodeId, 0);
            stMap.put(nodeId, stNode);
            stNodes.put(stNode, 1);
        } else {
            Node stNode = stMap.get(nodeId);
            stNodes.merge(stNode, 1, (oldVal, param) -> oldVal + param);
        }
        // 更新图结构 : 邻接表
        Node node = new Node(nodeId, pathId);
        Node stNode = stMap.get(nodeId);
        addEdge2adjList(stNode, node, 1);   // 换乘边
        addEdge2adjList(node, stNode, 1);   // 换乘边
    }

    @Override
    public void addMyPath2Product(MyPath myPath, Integer pathId) {
        // System.out.println("addMyPath2Product.");
        addNode2Map(myPath.getNode(0), pathId);
        for (int i = 1; i < myPath.size(); i++) {
            int fromNodeId = myPath.getNode(i - 1);
            int toNodeId = myPath.getNode(i);

            if (fromNodeId == toNodeId) {
                continue;
            }
            addNode2Map(toNodeId, pathId);
            Node fromNode = new Node(fromNodeId, pathId);
            Node toNode = new Node(toNodeId, pathId);
            addEdge2adjList(fromNode, toNode, 0);   // 邻接边
            addEdge2adjList(toNode, fromNode, 0);   // 邻接边
        }
    }

    private void delEdge4adjList(Node fromNode, Node toNode) {
        transferMatrix.delEdge4adjList(fromNode, toNode);
        priceMatrix.delEdge4adjList(fromNode, toNode);
        unpleasantMatrix.delEdge4adjList(fromNode, toNode);
    }

    private void delNode4Map(Integer nodeId, Integer pathId) {
        Node node = new Node(nodeId, pathId);
        Node stNode = stMap.get(nodeId);

        stNodes.merge(stNode, -1, (oldVal, param) -> oldVal + param);
        if (stNodes.get(stNode) == 0) {
            stNodes.remove(stNode);
            stMap.remove(nodeId);
        }
        delEdge4adjList(node, stNode);
        delEdge4adjList(stNode, node);
    }

    @Override
    public void removeMyPath4Product(MyPath myPath, Integer pathId) {
        // 删除结点与增加结点逻辑顺序正好相反
        // 先删边，再删结点
        for (int i = 0; i < myPath.size() - 1; i++) {
            int fromNodeId = myPath.getNode(i);
            int toNodeId = myPath.getNode(i + 1);

            if (fromNodeId == toNodeId) {
                continue;
            }
            Node fromNode = new Node(fromNodeId, pathId);
            Node toNode = new Node(toNodeId, pathId);
            delEdge4adjList(fromNode, toNode);
            delEdge4adjList(toNode, fromNode);

            delNode4Map(fromNodeId, pathId);
        }
        delNode4Map(myPath.getNode(myPath.size() - 1), pathId);
    }

    /* 最短问题 */
    @Override
    public void initResult() {
        super.initResult();
        this.transferMatrix.reset();
        this.priceMatrix.reset();
        this.unpleasantMatrix.reset();
    }

    public int getLeastTicketPrice(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        if (!isConnected(fromNodeId, toNodeId)) {
            throw new NodeNotConnectedException(fromNodeId, toNodeId);
        }
        return priceMatrix.getShortestPath(fromNodeId, toNodeId);
    }

    public int getLeastTransferCount(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        if (!isConnected(fromNodeId, toNodeId)) {
            throw new NodeNotConnectedException(fromNodeId, toNodeId);
        }
        return transferMatrix.getShortestPath(fromNodeId, toNodeId);
    }

    public int getLeastUnpleasantValue(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        if (!isConnected(fromNodeId, toNodeId)) {
            throw new NodeNotConnectedException(fromNodeId, toNodeId);
        }
        return unpleasantMatrix.getShortestPath(fromNodeId, toNodeId);
    }

    /* 连通块的计算逻辑移植到Graph类中 */
    @Override
    public int getConnectedBlockCount() {
        return super.getConnectedBlockCount();
    }

    /* There is no need to implement the method as follows. */

    //It is not required to implement, just for constructing the JML spec.
    public /*@pure@*/ boolean containsPathSequence(
            Path[] pseq) {
        return false;
    }

    //It is not required to implement, just for constructing the JML spec.
    public /*@pure@*/ boolean isConnectedInPathSequence(
            Path[] pseq, int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, PathNotFoundException {
        return false;
    }

    //It is not required to implement, just for constructing the JML spec.
    public /*@pure@*/ int getTicketPrice(
            Path[] pseq, int fromNodeId, int toNodeId) {
        return 0;
    }

    //It is not required to implement, just for constructing the JML spec.
    public /*@pure@*/ int getUnpleasantValue(
            Path path, int[] idx) {
        return 0;
    }

    public /*@pure@*/ int getUnpleasantValue(
            Path path, int fromIndex, int toIndex) {
        MyPath myPath = (MyPath) path;
        return Math.max(myPath.getUnpleasantValue(fromIndex),
                myPath.getUnpleasantValue(toIndex));
    }

    //It is not required to implement, just for constructing the JML spec.
    public /*@pure@*/ int getUnpleasantValue(
            Path[] pseq, int fromNodeId, int toNodeId) {
        return 0;
    }

}
