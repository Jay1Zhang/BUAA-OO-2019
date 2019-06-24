import homework.MyPath;
import homework.MyPathContainer;

public class TestMyPathContainer {
    public static void main(String[] args) {
        MyPathContainer pathContainer = new MyPathContainer();
        MyPath path1 = new MyPath(1,1,2,3);
        MyPath path2 = new MyPath(1,1,2,4);
        MyPath path3 = new MyPath(1,1,2,4);

        try {
            pathContainer.addPath(path1);
            pathContainer.addPath(path2);
            //pathContainer.addPath(path3);

            System.out.println(pathContainer.containsPath(path3));
            System.out.println(pathContainer.getPathId(path3));
            //pathContainer.removePathById(1);
        } catch (Exception e) {
            e.printStackTrace();
        }

    }
}
