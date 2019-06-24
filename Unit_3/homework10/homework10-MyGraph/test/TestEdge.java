public class TestEdge {
    public static void main(String[] args) {
        Edge edge1 = new Edge(803356400, -2142528590);
        Edge edge2 = new Edge(-2142528590, 803356400);

        System.out.println(edge1.hashCode());
        System.out.println(edge2.hashCode());
        System.out.println(edge1.equals(edge2));
        System.out.println(edge2.equals(edge1));
    }
}