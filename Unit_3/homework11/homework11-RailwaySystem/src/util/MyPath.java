package util;

import com.oocourse.specs3.models.Path;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

public class MyPath implements Path {
    private ArrayList<Integer> nodes = new ArrayList<Integer>();
    private HashSet<Integer> nodesSet = new HashSet<Integer>();

    public MyPath(int... nodeList) {
        for (int i = 0; i < nodeList.length; i++) {
            nodes.add(nodeList[i]);
            nodesSet.add(nodeList[i]);
        }
    }

    public /*@pure@*/int size() {
        return nodes.size();
    }

    public /*@pure@*/ boolean isValid() {
        if (nodes.size() >= 2) {
            return true;
        } else {
            return false;
        }
    }

    public /*@pure@*/ int getNode(int index) {
        if (index < 0 || index >= size()) {
            throw new IndexOutOfBoundsException();
        }
        return nodes.get(index);
    }

    public /*@pure@*/ boolean containsNode(int node) {
        return nodesSet.contains(node);
    }

    public /*pure*/ int getDistinctNodeCount() {
        return nodesSet.size();
    }

    public ArrayList<Integer> getNodesList() {
        return nodes;
    }

    public HashSet<Integer> getDistinctNodesSet() {
        return nodesSet;
    }

    public /*@pure@*/ int getUnpleasantValue(int nodeId) {
        if (nodesSet.contains(nodeId)) {
            return (int) Math.pow(4, (nodeId % 5 + 5) % 5);
        } else {
            return 0;
        }
    }

    @Override
    public Iterator<Integer> iterator() {
        return nodes.iterator();
    }

    @Override
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
    public boolean equals(Object obj) {
        if (obj == null || !(obj instanceof Path)) {
            return false;
        }

        Path path = (Path) obj;
        if (this.size() != path.size()) {
            return false;
        }

        for (int i = 0; i < path.size(); i++) {
            if (nodes.get(i) != path.getNode(i)) {
                return false;
            }
        }

        return true;
    }

    @Override
    public int hashCode() {
        return nodes.hashCode();
    }
}
