package util;

import com.oocourse.specs3.models.Graph;
import com.oocourse.specs3.models.NodeIdNotFoundException;
import com.oocourse.specs3.models.NodeNotConnectedException;
import com.oocourse.specs3.models.Path;
import com.oocourse.specs3.models.PathIdNotFoundException;
import com.oocourse.specs3.models.PathNotFoundException;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class MyGraph extends MyPathContainer implements Graph {
    private int connectedBlockCount = -1;
    // nodes set
    private HashMap<Integer, Integer> nodes = new HashMap<>();
    // <stNodeId, edNodeId> -> num
    private HashMap<Integer, HashMap<Integer, Integer>> adjList =
            new HashMap<>();
    // <stNodeId, edNodeId> -> distance
    private HashMap<Integer, HashMap<Integer, Integer>> shortestDist =
            new HashMap<>();

    /*
        Override - MyPathContainer
     */
    private void addNode(Integer nodeId) {
        if (nodes.containsKey(nodeId)) {
            nodes.merge(nodeId, 1, (oldVal, one) -> oldVal + one);
        } else {
            nodes.put(nodeId, 1);
        }
    }

    private void addEdge(Integer fromNodeId, Integer toNodeId) {
        if (adjList.containsKey(fromNodeId)) {
            HashMap<Integer, Integer> fromList = adjList.get(fromNodeId);
            if (fromList.containsKey(toNodeId)) {
                int num = fromList.get(toNodeId);
                fromList.put(toNodeId, num + 1);
            } else {
                fromList.put(toNodeId, 1);
            }
            adjList.put(fromNodeId, fromList);
        } else {
            HashMap<Integer, Integer> fromList = new HashMap<>();
            fromList.put(toNodeId, 1);
            adjList.put(fromNodeId, fromList);
        }
    }

    private void addMyPath(MyPath myPath) {
        addNode(myPath.getNode(0));
        for (int i = 1; i < myPath.size(); i++) {
            int fromNodeId = myPath.getNode(i - 1);
            int toNodeId = myPath.getNode(i);
            addNode(toNodeId);

            addEdge(fromNodeId, toNodeId);
            addEdge(toNodeId, fromNodeId);
        }
    }

    /* 在子类实现 */
    public void addMyPath2Product(MyPath myPath, Integer pathId) {}

    @Override
    public int addPath(Path path) {
        boolean isRepeated = super.containsPath(path);
        final int pathId = super.addPath(path);
        // fail to add path
        if (pathId == 0) { return 0; }
        // add repeated path, return pathId directly
        if (isRepeated) { return pathId; }
        // else
        // update graph and railway system
        addMyPath((MyPath) path);
        addMyPath2Product((MyPath) path, pathId);
        initResult();
        // and return pathId
        return pathId;
    }

    /**
     * Pre-Condition
     * 删除结点必定存在
     * @param nodeId
     */
    private void delNode(Integer nodeId) {
        int num = nodes.get(nodeId);
        if (num == 1) {
            nodes.remove(nodeId);
        } else {
            nodes.put(nodeId, num - 1);
        }
    }

    /**
     * Pre-Condition:
     * 待删除边一定存在
     * @param fromNodeId
     * @param toNodeId
     */
    private void delEdge(Integer fromNodeId, Integer toNodeId) {
        int num = adjList.get(fromNodeId).get(toNodeId);
        if (num == 1) {
            adjList.get(fromNodeId).remove(toNodeId);
            // 若该结点邻接表为空，remove
            if (adjList.get(fromNodeId).isEmpty()) {
                adjList.remove(fromNodeId);
            }
        } else {
            adjList.get(fromNodeId).put(toNodeId, num - 1);
        }
    }

    private void removeMyPath(MyPath myPath) {
        delNode(myPath.getNode(0));
        for (int i = 1; i < myPath.size(); i++) {
            int fromNodeId = myPath.getNode(i - 1);
            int toNodeId = myPath.getNode(i);
            delNode(toNodeId);

            delEdge(fromNodeId, toNodeId);
            delEdge(toNodeId, fromNodeId);
        }
    }

    /* 在子类实现 */
    public void removeMyPath4Product(MyPath myPath, Integer pathId) {}

    @Override
    public int removePath(Path path) throws PathNotFoundException {
        final int pathId = super.removePath(path);
        // update graph and railway system
        removeMyPath((MyPath) path);
        removeMyPath4Product((MyPath) path, pathId);
        initResult();

        return pathId;
    }

    @Override
    public void removePathById(int pathId) throws PathIdNotFoundException {
        Path path = super.getPathById(pathId);
        super.removePathById(pathId);
        // update graph and railway system
        removeMyPath((MyPath) path);
        removeMyPath4Product((MyPath) path, pathId);
        initResult();
    }

    /* MyGraph */
    public void initResult() {
        this.connectedBlockCount = -1;
        this.shortestDist.clear();
    }

    @Override
    public int getDistinctNodeCount() {
        return nodes.size();
    }

    public /*@pure@*/ boolean containsNode(int nodeId) {
        return nodes.containsKey(nodeId);
    }

    public /*@pure@*/ boolean containsEdge(int fromNodeId, int toNodeId) {
        if (adjList.containsKey(fromNodeId) &&
                adjList.get(fromNodeId).containsKey(toNodeId)) {
            return true;
        }
        return false;
    }

    public boolean isConnected(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException {
        if (!containsNode(fromNodeId)) {
            throw new NodeIdNotFoundException(fromNodeId);
        }
        if (!containsNode(toNodeId)) {
            throw new NodeIdNotFoundException(toNodeId);
        }
        // 若miss，计算单源最短路
        if (!shortestDist.containsKey(fromNodeId)) {
            updateDist2st(fromNodeId);
        }

        if (shortestDist.get(fromNodeId).containsKey(toNodeId)) {
            return true;
        } else {
            return false;
        }
    }

    public int getShortestPathLength(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        if (!isConnected(fromNodeId, toNodeId)) {
            throw new NodeNotConnectedException(fromNodeId, toNodeId);
        }
        return shortestDist.get(fromNodeId).get(toNodeId);
    }

    private void updateDist2st(int st) {
        HashMap<Integer,Integer> dist2st = new HashMap<>();
        LinkedList<Integer> queue = new LinkedList<>();
        HashSet<Integer> visited = new HashSet<>();
        dist2st.put(st,0);
        queue.addLast(st);
        visited.add(st);

        while (!queue.isEmpty()) {
            int ver = queue.removeFirst();
            HashMap<Integer,Integer> reachableMap = adjList.get(ver);
            // 遍历vertex的直接可达结点
            for (Integer ed: reachableMap.keySet()) {
                if (visited.contains(ed)) {
                    continue;
                }

                int dist = dist2st.get(ver);
                dist2st.put(ed, dist + 1);
                queue.addLast(ed);
                visited.add(ed);
            }
        }
        shortestDist.put(st, dist2st);
    }

    /* MyRailwaySystem */
    public int getConnectedBlockCount() {
        if (connectedBlockCount < 0) {
            calcConnectedBlockCount();
        }

        return connectedBlockCount;
    }

    private void calcConnectedBlockCount() {
        HashSet<Integer> visited = new HashSet<>();
        connectedBlockCount = 0;
        for (Integer st: nodes.keySet()) {
            if (visited.contains(st)) {
                continue;
            }
            connectedBlockCount++;

            LinkedList<Integer> queue = new LinkedList<>();
            queue.addLast(st);
            while (!queue.isEmpty()) {
                int ver = queue.removeFirst();
                if (visited.contains(ver)) {
                    continue;
                }
                visited.add(ver);

                HashMap<Integer,Integer> reachableMap = adjList.get(ver);
                for (Integer ed: reachableMap.keySet()) {
                    if (visited.contains(ed)) {
                        continue;
                    }
                    queue.addLast(ed);
                }
            }
        }
    }

}
