package factory;

import base.Node;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class RailwayGraphFactory implements GraphFactory {
    public static final int INFINITY = 0x3fffffff;

    private final int stepWeight;
    private final int switchWeight;

    // <stNode, edNode> -> edgeWeight
    private HashMap<Node, HashMap<Node, Integer>> adjList = new HashMap<>();
    // <fromNode, toNode> -> shortest distance
    private HashMap<Node, HashMap<Node, Integer>> ansMap = new HashMap<>();

    public RailwayGraphFactory(int stepWeight, int switchWeight) {
        this.stepWeight = stepWeight;
        this.switchWeight = switchWeight;
    }

    public Integer getEdgeWeight(Node fromNode, Node toNode, int type) {
        switch (type) {
            case 0: // 临边
                return 2 * stepWeight;
            case 1: // 换乘边
                return switchWeight;
            default:
                return -1;

        }
    }

    public void addEdge2adjList(Node fromNode, Node toNode, int edgeType) {
        if (adjList.containsKey(fromNode)) {
            HashMap<Node, Integer> fromList = adjList.get(fromNode);
            fromList.put(toNode, getEdgeWeight(fromNode, toNode, edgeType));
            adjList.put(fromNode, fromList);
        } else {
            HashMap<Node, Integer> fromList = new HashMap<>();
            fromList.put(toNode, getEdgeWeight(fromNode, toNode, edgeType));
            adjList.put(fromNode, fromList);
        }
    }

    public void delEdge4adjList(Node fromNode, Node toNode) {
        adjList.get(fromNode).remove(toNode);
    }

    @Override
    public void reset() {
        ansMap.clear();
    }

    /**
     * Pre-Condition:
     * isConnected(fromNodeId, toNodeId)
     * @param fromNodeId
     * @param toNodeId
     * @return
     */
    @Override
    public Integer getShortestPath(Integer fromNodeId, Integer toNodeId) {
        if (fromNodeId.equals(toNodeId)) {
            return 0;
        }
        Node stNode = new Node(fromNodeId, 0);
        Node edNode = new Node(toNodeId, 0);

        if (ansMap.containsKey(stNode) &&
                ansMap.get(stNode).containsKey(edNode) &&
                ansMap.get(stNode).get(edNode) != INFINITY) {
            return (ansMap.get(stNode).get(edNode) / 2) - switchWeight;
        }
        if (ansMap.containsKey(edNode) &&
                ansMap.get(edNode).containsKey(stNode) &&
                ansMap.get(edNode).get(stNode) != INFINITY) {
            return (ansMap.get(edNode).get(stNode) / 2) - switchWeight;
        }

        dijkstra(stNode, edNode);
        // newValue = newValue / 2 - switchWeight;
        return (ansMap.get(stNode).get(edNode) / 2) - switchWeight;
    }

    /*
        最后得到的answer要除以2，再减去一个换乘边权
     */
    private void dijkstra(Node stNode, Node edNode) {
        Set<Node> nodes = adjList.keySet();
        final HashSet<Node> wfound = new HashSet<>();
        HashSet<Node> queue = new HashSet<>();
        HashMap<Node, Integer> dist2st;

        // init dist[]
        if (ansMap.containsKey(stNode)) {
            dist2st = ansMap.get(stNode);
        } else {
            dist2st = new HashMap<>();
            dist2st.put(stNode, 0);
            queue.add(stNode);
        }
        for (Node node : nodes) {
            if (!dist2st.containsKey(node)) {
                dist2st.put(node, INFINITY);
            } else {
                queue.add(node);
            }
        }

        while (!queue.isEmpty()) {
            // get least dst;
            int dst = INFINITY;
            Node ver = new Node();
            for (Node each: queue) {
                if (!wfound.contains(each) && dist2st.get(each) < dst) {
                    dst = dist2st.get(each);
                    ver = each;
                }
            }
            queue.remove(ver);
            wfound.add(ver);

            HashMap<Node,Integer> dist2ver = adjList.get(ver);
            for (Node node: dist2ver.keySet()) {
                if (!wfound.contains(node)) {
                    if (dist2st.get(node) >
                            dist2st.get(ver) + dist2ver.get(node)) {
                        dist2st.put(node,
                                dist2st.get(ver) + dist2ver.get(node));
                        queue.add(node);

                        if (node.equals(edNode)) {
                            ansMap.put(stNode, dist2st);
                            return;
                        }
                    }
                }
            }

        }
        ansMap.put(stNode, dist2st);
    }

}

