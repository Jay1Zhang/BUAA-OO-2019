import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class Test {
    public static void main(String[] args) {
        /*
        HashSet<Integer> set = new HashSet<>();
        HashMap<Integer, HashSet<Integer>> res = new HashMap<>();

        set.add(1000);
        res.put(1, set);
        HashSet<Integer> temp = res.get(1);

        System.out.println(temp);
        System.out.println(res.get(1));

        temp.add(2000);

        System.out.println(temp);
        System.out.println(res.get(1));


        Set<String> parentAssoSet = new HashSet<>();
        Set<String> thisAssoSet = new HashSet<>();
        Set<String> newAssoSet = new HashSet<>();

        parentAssoSet.add("parent1");
        thisAssoSet.add("child1");
        parentAssoSet.add("parent2");
        thisAssoSet.add("child2");
        parentAssoSet.add("parent1");
        thisAssoSet.add("child1");
        parentAssoSet.add("share");
        thisAssoSet.add("share");

        // 尚未经过实践验证
        newAssoSet.addAll(parentAssoSet);
        newAssoSet.addAll(thisAssoSet);

        System.out.println(parentAssoSet);
        System.out.println(thisAssoSet);
        System.out.println(newAssoSet);
        */

        Integer integer = 1;
        addOne(integer);
        System.out.println("main: " + integer);
    }

    public static void addOne(Integer integer) {
        integer += 1;
        System.out.println("add1: " + integer);
    }
}
