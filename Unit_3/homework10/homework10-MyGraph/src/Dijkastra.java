import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;

public class Dijkastra {
    // <node, boolean>
    private HashMap<Integer, Integer> wfound = new HashMap<>();
    // <node, distance>
    private HashMap<Integer, Integer> dist = new HashMap<>();
    // <node, lastNode>
    private HashMap<Integer, Integer> paths = new HashMap<>();

    /**
     *
     * @param v0        源点
     * @param nodeSet   所有结点序列
     * @param weight    权重矩阵
     */
    public Dijkastra(final int v0, final Set<Integer> nodeSet,
                     final HashMap<Edge, Integer> weight) {
        ArrayList<Integer> nodeList = new ArrayList<>(nodeSet);
        int ver = 0;
        int minweight;

        for (int i = 0; i < nodeList.size(); i++) {
            ver = nodeList.get(i);
            Edge edge = new Edge(v0, ver);

            wfound.put(ver, 0);  // wfound[i]=false
            paths.put(ver, v0);  // paths[i]=v0
            // dist[i]=weight[v0][v]
            if (weight.containsKey(edge)) {
                dist.put(ver, weight.get(edge));
            } else {
                dist.put(ver, MyGraph.INFINITY);
            }
        }
        dist.put(v0, 0);
        wfound.put(v0, 1);

        for (int i = 0; i < nodeList.size() - 1; i++) {
            minweight = MyGraph.INFINITY;
            for (int j = 0; j < nodeList.size(); j++) {
                int tempV = nodeList.get(j);
                if (wfound.get(tempV) == 0 && dist.get(tempV) < minweight) {
                    ver = tempV;
                    minweight = dist.get(ver);
                }
            }
            wfound.put(ver, 1);
            for (int j = 0; j < nodeList.size(); j++) {
                int tempV = nodeList.get(j);
                Edge edge = new Edge(ver, tempV);

                if (!weight.containsKey(edge)) {
                    weight.put(edge, MyGraph.INFINITY);
                }

                if (wfound.get(tempV) == 0 &&
                        (minweight + weight.get(edge)) < dist.get(tempV)) {
                    dist.put(tempV, minweight + weight.get(edge));
                    paths.put(tempV, ver);
                }
            }
        }
    }

    public HashMap<Edge, Integer> getShortestDist(int v0) {
        HashMap<Edge, Integer> shortestDist = new HashMap<>();

        for (Integer ver: dist.keySet()) {
            Edge edge = new Edge(v0, ver);
            shortestDist.put(edge, dist.get(ver));
        }
        return shortestDist;
    }
}
