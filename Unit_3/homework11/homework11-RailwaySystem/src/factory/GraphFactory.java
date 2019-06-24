package factory;

public interface GraphFactory {
    void reset();

    Integer getShortestPath(Integer fromNodeId, Integer toNodeId);
}
