import java.util.HashMap;
import java.util.HashSet;

public class TestDij {
    public static void main(String[] args) {
        int v0 = 1;

        HashSet<Integer> nodeSet = new HashSet<>();
        nodeSet.add(1);
        nodeSet.add(2);
        nodeSet.add(3);

        HashMap<Edge, Integer> weight = new HashMap<>();
        Edge e1 = new Edge(1, 2);
        Edge e2 = new Edge(2, 3);
        weight.put(e1, 1);
        weight.put(e2, 1);


        //Edge e3 = new Edge(2, 1);
        //int value = weight.get(e3);



        Dijkastra dijkastra = new Dijkastra(v0, nodeSet, weight);

        HashMap<Edge, Integer> dist = dijkastra.getShortestDist(1);

        System.out.println(dist.toString());

    }
}
