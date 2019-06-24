import homework.MyPath;

public class TestMyPath {
    public static void main(String[] args) {
        MyPath path1 = new MyPath(2147483647, 2147483647, 2147483647);
        MyPath path2 = new MyPath(1,1,2,4, 2147483647);

        System.out.println(path1.hashCode());
        System.out.println(path2.hashCode());

    }
}
