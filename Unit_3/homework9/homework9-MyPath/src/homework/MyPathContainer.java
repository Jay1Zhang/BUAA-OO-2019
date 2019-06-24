package homework;

import com.oocourse.specs1.models.Path;
import com.oocourse.specs1.models.PathContainer;
import com.oocourse.specs1.models.PathIdNotFoundException;
import com.oocourse.specs1.models.PathNotFoundException;

import java.util.HashMap;

public class MyPathContainer implements PathContainer {
    //@ public instance model non_null Path[] pList;
    //@ public instance model non_null int[] pidList;
    private HashMap<Integer, MyPath> pathsById;
    private HashMap<MyPath, Integer> pathsBypt;
    private static int counter = 1;
    private static int distinctNodeCount = 0;

    public MyPathContainer() {
        pathsById = new HashMap<Integer, MyPath>();
        pathsBypt = new HashMap<MyPath, Integer>();
    }

    private void updDistNodeCnt() {
        HashMap<Integer, Integer> allNodesMap = new HashMap<Integer, Integer>();

        for (Integer pathId: pathsById.keySet()) {
            HashMap<Integer, Integer> nodesMap =
                    pathsById.get(pathId).getDistinctNodes();
            allNodesMap.putAll(nodesMap);
        }

        distinctNodeCount = allNodesMap.size();
        //System.out.println("current distinct count is " + distinctNodeCount);
    }

    //@ ensures \result == pList.length;
    public /*@pure@*/int size() {
        return pathsById.size();
    }

    /*@ requires path != null;
      @ assignable \nothing;
      @ ensures \result == (\exists int i; 0 <= i && i < pList.length;
      @                     pList[i].equals(path));
      @*/
    public /*@pure@*/ boolean containsPath(Path path) {
        return pathsBypt.containsKey(path);
    }

    /*@ ensures \result == (\exists int i; 0 <= i && i < pidList.length;
      @                      pidList[i] == pathId);
      @*/
    public /*@pure@*/ boolean containsPathId(int pathId) {
        return pathsById.containsKey(pathId);
    }

    /*@ public normal_behavior
      @ requires containsPathId(pathId);
      @ assignable \nothing;
      @ ensures (pidList.length == pList.length) &&
      @ (\exists int i; 0 <= i && i < pList.length;
      @     pidList[i] == pathId && \result == pList[i]);
      @ also
      @ public exceptional_behavior
      @ requires !containsPathId(pathId);
      @ assignable \nothing;
      @ signals_only PathIdNotFoundException;
      @*/
    public /*@pure@*/ Path getPathById(int pathId)
            throws PathIdNotFoundException {
        if (containsPathId(pathId)) {
            return pathsById.get(pathId);
        } else {
            throw new PathIdNotFoundException(pathId);
        }
    }

    /*@ public normal_behavior
      @ requires path != null && path.isValid() && containsPath(path);
      @ assignable \nothing;
      @ ensures (pidList.length == pList.length) &&
      @     (\exists int i; 0 <= i && i < pList.length;
      @         pList[i].equals(path) && pidList[i] == \result);
      @ also
      @ public exceptional_behavior
      @ signals (PathNotFoundException e) path == null;
      @ signals (PathNotFoundException e) !path.isValid();
      @ signals (PathNotFoundException e) !containsPath(path);
      @*/
    public /*@pure@*/ int getPathId(Path path) throws PathNotFoundException {
        if (path == null || !path.isValid() || !containsPath(path)) {
            throw new PathNotFoundException(path);
        } else {
            return pathsBypt.get(path);
        }
    }

    /*@ normal_behavior
      @ requires path != null && path.isValid();
      @ assignable pList, pidList;
      @ ensures (pidList.length == pList.length);
      @ ensures (\exists int i; 0 <= i && i < pList.length; pList[i] == path &&
      @           \result == pidList[i]);
      @ ensures !\old(containsPath(path)) ==>
      @          pList.length == (\old(pList.length) + 1) &&
      @          pidList.length == (\old(pidList.length) + 1);
      @ ensures (\forall int i; 0 <= i && i < \old(pList.length);
      @     containsPath(\old(pList[i])) && containsPathId(\old(pidList[i])));
      @ also
      @ normal_behavior
      @ requires path == null || path.isValid() == false;
      @ assignable \nothing;
      @ ensures \result == 0;
      @*/
    public int addPath(Path path) {
        if (path == null || !path.isValid()) {
            return 0;
        }

        if (pathsBypt.containsKey(path)) {
            return pathsBypt.get(path);
        }

        pathsById.put(counter, (MyPath) path);
        pathsBypt.put((MyPath) path, counter);
        counter++;
        updDistNodeCnt();

        return counter - 1;
    }

    /*@ public normal_behavior
      @ requires path != null && path.isValid() && \old(containsPath(path));
      @ assignable pList, pidList;
      @ ensures containsPath(path) == false;
      @ ensures (pidList.length == pList.length);
      @ ensures (\exists int i; 0 <= i &&
      @     i < \old(pList.length); \old(pList[i].equals(path)) &&
      @           \result == \old(pidList[i]));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathNotFoundException e) path == null;
      @ signals (PathNotFoundException e) path.isValid()==false;
      @ signals (PathNotFoundException e) !containsPath(path);
      @*/
    public int removePath(Path path) throws PathNotFoundException {
        if (path == null || !path.isValid() || !containsPath(path)) {
            throw new PathNotFoundException(path);
        }

        int pathId = pathsBypt.get(path);
        pathsById.remove(pathId);
        pathsBypt.remove(path);
        updDistNodeCnt();

        return pathId;
    }

    /*@ public normal_behavior
      @ requires \old(containsPathId(pathId));
      @ assignable pList, pidList;
      @ ensures pList.length == pidList.length;
      @ ensures (\forall int i; 0 <= i
      @     && i < pidList.length; pidList[i] != pathId);
      @ ensures (\forall int i; 0 <= i &&
      @     i < pList.length; !pList[i].equals(\old(getPathById(pathId))));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathIdNotFoundException e) !containsPathId(pathId);
      @*/
    public void removePathById(int pathId) throws PathIdNotFoundException {
        if (!pathsById.containsKey(pathId)) {
            throw new PathIdNotFoundException(pathId);
        }

        MyPath path = pathsById.get(pathId);
        pathsById.remove(pathId);
        pathsBypt.remove(path);
        updDistNodeCnt();

        //System.out.println("remove path: " + path + " by path id: " + pathId);
    }

    /*@ ensures
      @ (\exists int[] arr;
      @ (\forall int i, j; 0 <= i && i < j && j < arr.length; arr[i] != arr[j]);
      @ (\forall int i; 0 <= i && i < arr.length;
      @     (\exists Path p; this.containsPath(p); p.containsNode(arr[i])))
      @  &&(\forall Path p; this.containsPath(p);
      @         (\forall int node; p.containsNode(node);
      @         (\exists int i; 0 <= i && i < arr.length; node == arr[i])))
      @  &&(\result == arr.length));
      @*/
    //在容器全局范围内查找不同的节点数
    public /*@pure@*/int getDistinctNodeCount() {
        return distinctNodeCount;
    }
}
