package factory;

import base.Node;

import java.util.HashMap;

public class UnpleasantGraphFactory extends RailwayGraphFactory
        implements GraphFactory {
    private static final int switchWeight = 32;
    private static final HashMap<Integer, Integer> nodeWeight =
            new HashMap<Integer, Integer>() {{
                put(0, 1);
                put(1, 4);
                put(2, 16);
                put(3, 64);
                put(4, 256);
            }};

    public UnpleasantGraphFactory() {
        super(-1, 32);
    }

    private Integer getNodeWeight(Node node) {
        int category = (node.getNodeId() % 5 + 5) % 5;
        return nodeWeight.get(category);
    }

    @Override
    public Integer getEdgeWeight(Node fromNode, Node toNode, int type) {
        switch (type) {
            case 0: // 临边
                return 2 * Math.max(
                        getNodeWeight(fromNode), getNodeWeight(toNode));
            case 1: // 换乘边
                return switchWeight;
            default:
                return -1;
        }
    }

}
