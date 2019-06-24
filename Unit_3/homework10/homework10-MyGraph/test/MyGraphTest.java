import com.oocourse.specs2.models.NodeIdNotFoundException;
import com.oocourse.specs2.models.NodeNotConnectedException;
import com.oocourse.specs2.models.PathNotFoundException;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;

public class MyGraphTest {
    @Test
    public void containsNode() {
        MyGraph g = new MyGraph();
        assertEquals(1, g.addPath(
                new MyPath(1, 7, 99, 6, 8, 54, 8, 5, -4, -2)));
        assertEquals(2, g.addPath(
                new MyPath(5, 123, 6, 3, 8, 55, 22, 4, -2)));
        assertEquals(1, g.addPath(
                new MyPath(1, 7, 99, 6, 8, 54, 8, 5, -4, -2)));
        assertEquals(0, g.addPath(new MyPath(34556)));
        assertEquals(0, g.addPath(new MyPath()));
        assertTrue(g.containsNode(8));
        assertTrue(g.containsNode(1));
        assertFalse(g.containsNode(34));
        assertFalse(g.containsNode(-1294));
        System.out.println("containsNode() tests cases passed!");
    }

    @Test
    public void containsEdge() {
        MyGraph g = new MyGraph();
        g.addPath(new MyPath(1, 2, 2, 3, 3, 4, 5));
        g.addPath(new MyPath(3, 2, 2, 7, 8, 12, -5, 222));
        assertTrue(g.containsEdge(2, 2));
        assertTrue(g.containsEdge(3, 3));
        assertTrue(g.containsEdge(2, 3));
        assertTrue(g.containsEdge(3, 4));
        assertFalse(g.containsEdge(1, 1));
        assertFalse(g.containsEdge(1, 3));
        assertFalse(g.containsEdge(4, 1));
        try {
            g.removePath(new MyPath(1, 2, 2, 3, 3, 4, 5));
        } catch (PathNotFoundException e) {
            e.printStackTrace();
        }
        assertTrue(g.containsEdge(2, 3));
        assertTrue(g.containsEdge(2, 2));
        assertFalse(g.containsEdge(1, 1));
        assertFalse(g.containsEdge(2, 1));
        System.out.println("containsEdge() tests cases passed!");
    }

    @Test
    public void isConnected() {
        MyGraph g = new MyGraph();
        g.addPath(new MyPath(1, 2, 3, 4, 8, 9, 3, 1, 5));
        g.addPath(new MyPath(5, 123, 6, 31, 8, 55, 22, 4, -2));
        g.addPath(new MyPath(6, 22, 22, 33));
        g.addPath(new MyPath(7, 35, 41, 52));
        try {
            assertTrue(g.isConnected(1, 22));
            assertTrue(g.isConnected(4, -2));
            assertTrue(g.isConnected(55, 55));
            assertTrue(g.isConnected(1, 33));
            assertFalse(g.isConnected(1, 52));
        } catch (NodeIdNotFoundException e) {
            e.printStackTrace();
        }
        try {
            assertFalse(g.isConnected(54, 43));
        } catch (NodeIdNotFoundException e) {
            assertEquals(e.toString(), "com.oocourse.specs2.models." +
                    "NodeIdNotFoundException: Node id not found - 54.");
        }
        try {
            assertFalse(g.isConnected(33, -124));
        } catch (NodeIdNotFoundException e) {
            assertEquals(e.toString(), "com.oocourse.specs2.models." +
                    "NodeIdNotFoundException: Node id not found - -124.");
        }
        System.out.println("isConnected() tests cases passed!");
    }

    @Test
    public void getShortestPathLength() {
        MyGraph g = new MyGraph();
        g.addPath(new MyPath(1, 2, 3, 4, 8, 9, 3, 1, 5));
        g.addPath(new MyPath(5, 123, 6, 3, 8, 55, -666, 22, 4, -2));
        g.addPath(new MyPath(11, 22, 22, 33, 55));
        g.addPath(new MyPath(7, 35, 41, 52));
        try {
            assertEquals(g.getShortestPathLength(1, 8), 2);
            assertEquals(g.getShortestPathLength(-2, 5), 4);
            assertEquals(g.getShortestPathLength(22, 22), 0);
            assertEquals(g.getShortestPathLength(55, 4), 2);
            assertEquals(g.getShortestPathLength(55, 22), 2);
        } catch (NodeIdNotFoundException | NodeNotConnectedException e) {
            e.printStackTrace();
        }
        try {
            assertEquals(g.getShortestPathLength(518, 4), 100000);
        } catch (NodeIdNotFoundException | NodeNotConnectedException e) {
            assertEquals(e.toString(), "com.oocourse.specs2.models." +
                    "NodeIdNotFoundException: Node id not found - 518.");
        }
        try {
            assertEquals(g.getShortestPathLength(33, -129424), 100000);
        } catch (NodeIdNotFoundException | NodeNotConnectedException e) {
            assertEquals(e.toString(), "com.oocourse.specs2.models." +
                    "NodeIdNotFoundException: Node id not found - -129424.");
        }
        try {
            assertEquals(g.getShortestPathLength(35, -666), 100000);
        } catch (NodeIdNotFoundException | NodeNotConnectedException e) {
            assertEquals(e.toString(), "com.oocourse.specs2.models.Nod" +
                    "eNotConnectedException: Node 35 and -666 not connected.");
        }
        System.out.println("getShortestPathLength() tests cases passed!");
    }

    @Test
    public void size() {
    }

    @Test
    public void containsPath() {
    }

    @Test
    public void containsPathId() {
    }

    @Test
    public void getPathById() {
    }

    @Test
    public void getPathId() {
    }

    @Test
    public void addPath() {
    }

    @Test
    public void removePath() {
    }

    @Test
    public void removePathById() {
    }

    @Test
    public void getDistinctNodeCount() {
    }
}