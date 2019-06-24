package homework;

import com.oocourse.specs1.models.Path;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

public class MyPath implements Path {
    // Iterable<Integer>和Comparable<Path>接口的规格请参阅JDK
    private ArrayList<Integer> nodes = new ArrayList<Integer>();
    private HashMap<Integer,Integer> nodesMap = new HashMap<Integer, Integer>();

    public MyPath(int... nodeList) {
        for (int i = 0; i < nodeList.length; i++) {
            nodes.add(nodeList[i]);
            nodesMap.put(nodeList[i], i);
        }
    }

    /*@ also
      @ ensures \result == nodes.length;
      @*/
    public /*@pure@*/int size() {
        return nodes.size();
    }

    /*@ also
      @ requires index >= 0 && index < size();
      @ assignable \nothing;
      @ ensures \result == nodes[index];
      @*/
    public /*@pure@*/ int getNode(int index) {
        if (index < 0 || index >= size()) {
            throw new IndexOutOfBoundsException();
        }
        return nodes.get(index);
    }

    /*@ also
      @ ensures \result ==
      @ (\exists int i; 0 <= i && i < nodes.length; nodes[i] == node);
      @*/
    public /*@pure@*/ boolean containsNode(int node) {
        return nodesMap.containsKey(node);
    }

    /*@ also
      @ ensures
      @ (\exists int[] arr;
      @ (\forall int i, j; 0 <= i && i < j && j < arr.length; arr[i] != arr[j]);
      @     (\forall int i; 0 <= i && i < arr.length;this.containsNode(arr[i]))
      @           && (\forall int node; this.containsNode(node);
      @             (\exists int j; 0 <= j && j < arr.length; arr[j] == node))
      @           && (\result == arr.length));
      @*/
    // 不同节点个数
    public /*pure*/ int getDistinctNodeCount() {
        return nodesMap.size();
    }

    public HashMap<Integer, Integer> getDistinctNodes() {
        return nodesMap;
    }

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Path;
      @ assignable \nothing;
      @ ensures \result == (((Path) obj).nodes.length == nodes.length) &&
      @             (\forall int i; 0 <= i && i < nodes.length;
      @                 nodes[i] == ((Path) obj).nodes[i]);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Path);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public boolean equals(Object obj) {
        if (obj == null || !(obj instanceof Path)) {
            return false;
        }

        Path path = (Path) obj;
        if (this.size() != path.size()) {
            return false;
        }

        if (this.hashCode() != path.hashCode()) {
            return false;
        }

        for (int i = 0; i < path.size(); i++) {
            if (nodes.get(i) != path.getNode(i)) {
                return false;
            }
        }

        return true;
    }

    /*
     @ also
     @ ensures \result == (nodes.length >= 2);
     @*/
    public /*@pure@*/ boolean isValid() {
        if (nodes.size() >= 2) {
            return true;
        } else {
            return false;
        }
    }

    public Iterator<Integer> iterator() {
        return nodes.iterator();
    }

    public int compareTo(Path p) {
        int len1 = this.size();
        int len2 = p.size();
        int lim = Math.min(len1, len2);

        int k = 0;
        while (k < lim) {
            int v1 = this.getNode(k);
            int v2 = p.getNode(k);

            if (v1 != v2) {
                return Integer.compare(v1, v2);
            }
            k++;
        }
        return len1 - len2;
    }

    @Override
    public int hashCode() {
        int hashCode = 0;
        int mod = 2147483647;

        for (int i = 0; i < size(); i++) {
            int key = nodes.get(i);

            key = ~key + (key << 15); // key = (key << 15) - key - 1;
            key = key ^ (key >>> 12);
            key = key + (key << 2);
            key = key ^ (key >>> 4);
            key = key * 2057; // key = (key + (key << 3)) + (key << 11);
            key = key ^ (key >>> 16);

            hashCode = (hashCode + key) % mod;
        }

        return hashCode;
    }
}
