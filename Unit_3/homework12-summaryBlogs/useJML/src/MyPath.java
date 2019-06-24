
public class MyPath {
    //@ public instance model non_null int[] nodes;
    public int[] myNodes = new int[1024];

    public MyPath(int... nodeList) {
        for (int i = 0; i < nodeList.length; i++) {
            myNodes[i] = nodeList[i];
        }
    }

    /*
      @ ensures \result == nodes.length;
      @*/
    public /*@pure@*/int size() {
        return myNodes.length;
    }

    /*
      @ requires index >= 0 && index < size();
      @ assignable \nothing;
      @ ensures \result == nodes[index];
      @*/
    public /*@pure@*/ int getNode(int index) {
        if (index < 0 || index >= size()) {
            throw new IndexOutOfBoundsException();
        }
        return myNodes[index];
    }

    /*
      @ ensures \result ==
      @ (\exists int i; 0 <= i && i < nodes.length; nodes[i] == node);
      @*/
    public /*@pure@*/ boolean containsNode(int node) {
        for (int i = 0; i < myNodes.length; i++) {
            if (myNodes[i] == node) {
                return true;
            }
        }
        return false;
    }

    /*
      @ ensures
      @ (\exists int[] arr;
      @ (\forall int i, j; 0 <= i && i < j && j < arr.length; arr[i] != arr[j]);
      @     (\forall int i; 0 <= i && i < arr.length;this.containsNode(arr[i]))
      @           && (\forall int node; this.containsNode(node);
      @             (\exists int j; 0 <= j && j < arr.length; arr[j] == node))
      @           && (\result == arr.length));
      @*/
    public /*pure*/ int getDistinctNodeCount() {
        return 0;
    }

    /*
     @ ensures \result == (nodes.length >= 2);
     @*/
    public /*@pure@*/ boolean isValid() {
        if (myNodes.length >= 2) {
            return true;
        } else {
            return false;
        }
    }

}
