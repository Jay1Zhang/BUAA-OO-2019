import com.oocourse.specs2.models.Graph;
import com.oocourse.specs2.models.NodeIdNotFoundException;
import com.oocourse.specs2.models.NodeNotConnectedException;
import com.oocourse.specs2.models.Path;
import com.oocourse.specs2.models.PathIdNotFoundException;
import com.oocourse.specs2.models.PathNotFoundException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class MyGraph extends MyPathContainer implements Graph {
    public static final int INFINITY = 100007;
    // <node, num in paths>
    private final HashMap<Integer, Integer> nodeMap;
    // <edge, num>
    private final HashMap<Edge, Integer> edgeMap;
    // <edge, weight>
    private final HashMap<Edge, Integer> weight;
    // <edge, shortest distance> by Dijkastra
    private HashMap<Edge, Integer> shortestDist;

    public MyGraph() {
        nodeMap = new HashMap<Integer, Integer>();
        edgeMap = new HashMap<Edge, Integer>();
        weight = new HashMap<Edge, Integer>();
        shortestDist = new HashMap<Edge, Integer>();
    }

    @Override
    public int addPath(Path path) {
        boolean isRepeated = super.containsPath(path);
        int pathId = super.addPath(path);

        if (pathId == 0) {
            // fail to add path
            return 0;
        } else if (isRepeated) {
            // add repeated path, return pathId directly
            return pathId;
        }
        // else, update graph
        MyPath myPath = (MyPath) path;
        // ATTENTION, here can be optimized.
        // 1. update nodeMap
        HashSet<Integer> nodeSet = myPath.getDistinctNodesSet();
        for (Integer key: nodeSet) {
            if (nodeMap.containsKey(key)) {
                nodeMap.put(key, nodeMap.get(key) + 1);
            } else {
                nodeMap.put(key, 1);
            }
        }
        // 2. update edgeMap
        // 3. update weight matrix
        ArrayList<Integer> nodesList = myPath.getNodesList();
        for (int i = 0; i < nodesList.size() - 1; i++) {
            int fromNode = nodesList.get(i);
            int toNode = nodesList.get(i + 1);
            Edge edge = new Edge(fromNode, toNode);

            if (edgeMap.containsKey(edge)) {
                edgeMap.put(edge, edgeMap.get(edge) + 1);
            } else {
                edgeMap.put(edge, 1);
            }

            weight.put(edge, 1); // edge.getWeight
        }

        // 4. clear shortest distance info
        shortestDist = new HashMap<Edge, Integer>();
        // and return pathId
        return pathId;
    }

    public void removeMyPath(MyPath myPath) {
        // ATTENTION, here can be optimized.
        // 1. update nodeMap
        HashSet<Integer> nodeSet = myPath.getDistinctNodesSet();
        for (Integer key: nodeSet) {
            if (nodeMap.get(key) == 1) {
                nodeMap.remove(key);
            } else {
                nodeMap.put(key, nodeMap.get(key) - 1);
            }
        }
        // 2. update edgeMap
        // 3. update weight matrix
        ArrayList<Integer> nodesList = myPath.getNodesList();
        for (int i = 0; i < nodesList.size() - 1; i++) {
            int fromNode = nodesList.get(i);
            int toNode = nodesList.get(i + 1);
            Edge edge = new Edge(fromNode, toNode);

            if (edgeMap.get(edge) == 1) {
                edgeMap.remove(edge);
                weight.remove(edge);
            } else {
                edgeMap.put(edge, edgeMap.get(edge) - 1);
            }
        }
        // 4. clear shortest distance info
        shortestDist = new HashMap<Edge, Integer>();
    }

    @Override
    public int removePath(Path path) throws PathNotFoundException {
        final int pathId = super.removePath(path);
        // update graph
        removeMyPath((MyPath) path);
        // and return pathId
        return pathId;
    }

    @Override
    public void removePathById(int pathId) throws PathIdNotFoundException {
        MyPath myPath = (MyPath) super.getPathById(pathId);
        super.removePathById(pathId);
        removeMyPath(myPath);
    }

    /*@ ensures \result == (\exists Path path; path.isValid()
      @ && containsPath(path); path.containsNode(nodeId));
      @*/
    public /*@pure@*/ boolean containsNode(int nodeId) {
        return nodeMap.containsKey(nodeId);
    }

    /*@ ensures \result == (\exists Path path; path.isValid()
      @ && containsPath(path);
      @      (\exists int i; 0 <= i && i < path.size() - 1;
      @ (path.getNode(i) == fromNodeId && path.getNode(i + 1) == toNodeId)||
      @    (path.getNode(i) == toNodeId && path.getNode(i + 1) == fromNodeId)));
      @*/
    public /*@pure@*/ boolean containsEdge(int fromNodeId, int toNodeId) {
        Edge edge = new Edge(fromNodeId, toNodeId);
        return edgeMap.containsKey(edge);
    }

    /*@ normal_behavior
      @ requires (\exists Path path; path.isValid() && containsPath(path);
      @ path.containsNode(fromNodeId)) &&
      @          (\exists Path path; path.isValid() && containsPath(path);
      @ path.containsNode(toNodeId));
      @ assignable \nothing;
      @ ensures (fromNodeId != toNodeId) ==> \result == (\exists int[] npath;
      @ npath.length >= 2 && npath[0] == fromNodeId
      @ && npath[npath.length - 1] == toNodeId;
      @                     (\forall int i; 0 <= i && (i < npath.length - 1);
      @ containsEdge(npath[i], npath[i + 1])));
      @ ensures (fromNodeId == toNodeId) ==> \result == true;
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e)
      @ (\forall Path path; containsPath(path); !path.containsNode(fromNodeId));
      @ signals
      @ (NodeIdNotFoundException e)
      @ (\forall Path path; containsPath(path); !path.containsNode(toNodeId));
      @*/
    public boolean isConnected(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException {
        if (!containsNode(fromNodeId)) {
            throw new NodeIdNotFoundException(fromNodeId);
        } else if (!containsNode(toNodeId)) {
            throw new NodeIdNotFoundException(toNodeId);
        }

        Edge edge = new Edge(fromNodeId, toNodeId);
        if (!shortestDist.containsKey(edge)) {
            // if miss, update TLB
            update(fromNodeId);
            /*
            Dijkastra dijkastra = new Dijkastra(
                    fromNodeId, nodeMap.keySet(), weight);
            HashMap<Edge, Integer> dist2v0 =
                    dijkastra.getShortestDist(fromNodeId);
            shortestDist.putAll(dist2v0);
            */
        }
        // The edge is bound to exist after updating,
        // but it may be INFINITY, that is not CONNECTED
        // if (shortestDist.get(edge) == INFINITY) {
        if (!shortestDist.containsKey(edge)) {
            // if still miss, not connected
            return false;
        } else {
            return true;
        }
    }

    /*@ normal_behavior
      @ requires (\exists Path path; path.isValid()
      @ && containsPath(path); path.containsNode(fromNodeId)) &&
      @          (\exists Path path; path.isValid()
      @ && containsPath(path); path.containsNode(toNodeId));
      @ assignable \nothing;
      @ ensures (fromNodeId != toNodeId) ==>
      @ (\exists int[] spath; spath.length >= 2 &&
      @     spath[0] == fromNodeId && spath[spath.length - 1] == toNodeId;
      @             (\forall int i; 0 <= i &&
      @         (i < spath.length - 1); containsEdge(spath[i], spath[i + 1])) &&
      @             (\forall Path p; p.isValid()
      @         && p.getNode(0) == fromNodeId &&
      @             p.getNode(p.size() - 1) == toNodeId &&
      @               (\forall int i; 0 <= i && (i < p.size() - 1);
      @         containsEdge(p.getNode(i), p.getNode(i + 1)));
       @        p.size() >= spath.length) &&
      @             (\result == spath.length - 1));
      @ ensures (fromNodeId == toNodeId) ==> \result == 0;
      @ also
      @ exceptional_behavior
      @ signals (NodeIdNotFoundException e)
      @     (\forall Path path; containsPath(path);
      @     !path.containsNode(fromNodeId));
      @ signals (NodeIdNotFoundException e)
      @     (\forall Path path; containsPath(path);
      @     !path.containsNode(toNodeId));
      @ signals (NodeNotConnectedException e)
      @ !(\exists int[] npath; npath.length >= 2 &&
      @     npath[0] == fromNodeId && npath[npath.length - 1] == toNodeId;
      @              (\forall int i; 0 <= i && (i < npath.length - 1);
       @        containsEdge(npath[i], npath[i + 1])));
      @*/
    public int getShortestPathLength(int fromNodeId, int toNodeId)
            throws NodeIdNotFoundException, NodeNotConnectedException {
        if (!isConnected(fromNodeId, toNodeId)) {
            throw new NodeNotConnectedException(fromNodeId, toNodeId);
        } else {
            return shortestDist.get(new Edge(fromNodeId, toNodeId));
        }
    }

    private void update(int st) {
        LinkedList<Integer> queue = new LinkedList<>();
        queue.addLast(st);
        HashMap<Integer, Integer> visited = new HashMap<>();
        visited.putAll(nodeMap);
        visited.put(st, -1);
        shortestDist.put(new Edge(st, st), 0);

        while (!queue.isEmpty()) {
            int ver = queue.removeFirst();
            // 遍历vertex的直接可达矩阵
            for (Integer ed: nodeMap.keySet()) {
                if (!edgeMap.containsKey(new Edge(ver, ed)) ||
                        visited.get(ed) == -1) {
                    // 若不可达或已被访问过
                    continue;
                } else {
                    int num = shortestDist.get(new Edge(st, ver));
                    shortestDist.put(new Edge(st, ed), num + 1);
                    queue.addLast(ed);
                    visited.put(ed, -1);
                }
            }
        }
    }

}
