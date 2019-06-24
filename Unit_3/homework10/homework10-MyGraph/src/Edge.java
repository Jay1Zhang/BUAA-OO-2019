/*
    undirected graph
 */
public class Edge {
    private final int fromNodeId;
    private final int toNodeId;
    private final int weight;

    public Edge(int fromNodeId, int toNodeId) {
        this.fromNodeId = fromNodeId;
        this.toNodeId = toNodeId;
        this.weight = 1;
    }

    public int getFromNodeId() {
        //return pair.getKey();
        return fromNodeId;
    }

    public int getToNodeId() {
        //return pair.getValue();
        return toNodeId;
    }

    public int getWeight() {
        return weight;
    }

    @Override
    public boolean equals(Object obj) {
        Edge edge = (Edge) obj;
        if (this.getFromNodeId() == edge.getFromNodeId()
                && this.getToNodeId() == edge.getToNodeId()) {
            return true;
        } else if (this.getFromNodeId() == edge.getToNodeId()
                && this.getToNodeId() == edge.getFromNodeId()) {
            return true;
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        int mod = 2147483647;
        int key = (fromNodeId * toNodeId) % mod;

        key = ~key + (key << 15); // key = (key << 15) - key - 1;
        key = key ^ (key >>> 12);
        key = key + (key << 2);
        key = key ^ (key >>> 4);
        key = key * 2057; // key = (key + (key << 3)) + (key << 11);
        key = key ^ (key >>> 16);

        return key;
    }
}
