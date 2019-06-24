package util;

import com.oocourse.specs3.models.Path;
import com.oocourse.specs3.models.PathContainer;
import com.oocourse.specs3.models.PathIdNotFoundException;
import com.oocourse.specs3.models.PathNotFoundException;

import java.util.HashMap;

public class MyPathContainer implements PathContainer {
    private HashMap<Integer, Path> id2Path;
    private HashMap<Path, Integer> path2Id;
    private static int pathIdCnt = 0;

    public MyPathContainer() {
        id2Path = new HashMap<>();
        path2Id = new HashMap<>();
    }

    public /*@pure@*/int size() {
        return id2Path.size();
    }

    public /*@pure@*/ boolean containsPath(Path path) {
        return path2Id.containsKey(path);
    }

    public /*@pure@*/ boolean containsPathId(int pathId) {
        return id2Path.containsKey(pathId);
    }

    public /*@pure@*/ Path getPathById(int pathId)
            throws PathIdNotFoundException {
        if (!containsPathId(pathId)) {
            throw new PathIdNotFoundException(pathId);
        }

        return id2Path.get(pathId);
    }

    public /*@pure@*/ int getPathId(Path path) throws PathNotFoundException {
        if (path == null || !path.isValid() || !containsPath(path)) {
            throw new PathNotFoundException(path);
        }

        return path2Id.get(path);
    }

    public int addPath(Path path) {
        if (path == null || !path.isValid()) {
            return 0;
        }

        if (path2Id.containsKey(path)) {
            return path2Id.get(path);
        }

        pathIdCnt++;
        id2Path.put(pathIdCnt, path);
        path2Id.put(path, pathIdCnt);

        return pathIdCnt;
    }

    public int removePath(Path path) throws PathNotFoundException {
        if (path == null || !path.isValid() || !containsPath(path)) {
            throw new PathNotFoundException(path);
        }

        int pathId = path2Id.get(path);
        id2Path.remove(pathId);
        path2Id.remove(path);

        return pathId;
    }

    public void removePathById(int pathId) throws PathIdNotFoundException {
        if (!id2Path.containsKey(pathId)) {
            throw new PathIdNotFoundException(pathId);
        }

        Path path = id2Path.get(pathId);
        id2Path.remove(pathId);
        path2Id.remove(path);

        //System.out.println("remove path: " + path + " by path id: " + pathId);
    }

    /* 在子类实现 */
    public /*@pure@*/int getDistinctNodeCount() {
        return -1;
    }
}
