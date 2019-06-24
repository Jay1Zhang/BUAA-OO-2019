public class Test {
    public static void main(String[] args) {

        MyGraph myGraph = new MyGraph();
        MyPath myPath = new MyPath(1, 2);
        try {
            myGraph.removePath(myPath);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
