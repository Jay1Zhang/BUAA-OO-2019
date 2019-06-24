import base.Node;
import com.oocourse.specs3.models.Path;
import org.omg.CORBA.INTERNAL;
import util.MyPath;
import util.MyRailwaySystem;

import java.util.HashMap;

public class Test {
    public static void main(String[] args) {
        /*
        HashMap<Node, Integer> nodes = new HashMap<>();
        Node node1 = new Node(2, 1);
        Node node2 = new Node(2, 1);

        nodes.put(node1, 3);

        System.out.println(nodes.get(node1));
        System.out.println(nodes.get(node2));
*/

        try {
            MyRailwaySystem railwaySystem = new MyRailwaySystem();
            Path path1 = new MyPath(1, 2);
            Path path2 = new MyPath(2, 3);
            railwaySystem.addPath(path1);
            railwaySystem.addPath(path2);

            railwaySystem.getLeastTicketPrice(1, 3);
        } catch (Exception e) {
            e.printStackTrace();
        }

        /*
        HashMap<Integer, HashMap<Integer, Integer>> container = new HashMap<>();
        HashMap<Integer, Integer> temp = new HashMap<>();

        temp.put(1, 124);
        temp.put(2, 125);
        container.put(1001, temp);

        System.out.println(container.get(1001));

        System.out.println(container.get(1001).containsKey(1));
        System.out.println(container.get(1001).containsKey(2));
        container.get(1001).remove(2);
        System.out.println(container.get(1001).containsKey(1));
        System.out.println(container.get(1001).containsKey(2));
        container.get(1001).remove(1);
        System.out.println(container.get(1001).containsKey(1));
        System.out.println(container.get(1001).containsKey(2));
        System.out.println(container.get(1001).isEmpty());
        */
    }
}
