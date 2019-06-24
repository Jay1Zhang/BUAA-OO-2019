package base;

public class Node {
    private int nodeId;
    private int pathId;

    public Node() {}

    public Node(int nodeId, int pathId) {
        this.nodeId = nodeId;
        this.pathId = pathId;
    }

    public int getNodeId() {
        return nodeId;
    }

    public int getPathId() {
        return pathId;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof Node)) {
            return false;
        }

        if (((Node)obj).nodeId != this.nodeId) {
            return false;
        }
        if (((Node)obj).pathId != this.pathId) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        return Integer.hashCode(nodeId) * Integer.hashCode(pathId);
    }

    @Override
    public String toString() {
        return "Node: ->hashCode: " + hashCode()
                + " \t->NodeId: " + nodeId + " \t->pathId: " + pathId;
    }
}
