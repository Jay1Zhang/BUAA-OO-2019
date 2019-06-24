package homework;

import org.junit.Test; 
import org.junit.Before; 
import org.junit.After;

import java.util.HashMap;
import java.util.Iterator;

import static org.junit.Assert.*;

/** 
* MyPath Tester. 
* 
* @author <Authors name> 
* @since <pre>ËÄÔÂ 29, 2019</pre> 
* @version 1.0 
*/ 
public class MyPathTest { 

@Before
public void before() throws Exception {
    System.out.println("Method Test Start");
} 

@After
public void after() throws Exception {
    System.out.println("Method Test End");
} 

/** 
* 
* Method: size() 
* 
*/ 
@Test
public void testSize() throws Exception { 
//TODO: Test goes here...
    int[] array = {1,2,3,4,4,3,2,1,2,2,2,2,4,4};
    MyPath path = new MyPath(array);

    assertEquals(array.length, path.size());

} 

/** 
* 
* Method: getNode(int index) 
* 
*/ 
@Test
public void testGetNode() throws Exception { 
//TODO: Test goes here...
    int[] array = {1,2,3,4};
    MyPath path = new MyPath(array);

    int i = 0;
    assertEquals(array[i], path.getNode(i));
} 

/** 
* 
* Method: containsNode(int node) 
* 
*/ 
@Test
public void testContainsNode() throws Exception { 
//TODO: Test goes here...
    MyPath path1 = new MyPath(1,2,3,4,4,3,2,1,2,4,3,1,1,1,1,1,1,1,1,1,1,1,2);

    assertEquals(true, path1.containsNode(2));
} 

/** 
* 
* Method: getDistinctNodeCount() 
* 
*/ 
@Test
public void testGetDistinctNodeCount() throws Exception { 
//TODO: Test goes here...
    MyPath path1 = new MyPath(1,2,3,4,4,3,2,1,2,4,3,1,1,1,1,1,1,1,1,1,1,1,2);

    assertEquals(4, path1.getDistinctNodeCount());
} 

/** 
* 
* Method: getDistinctNodes() 
* 
*/ 
@Test
public void testGetDistinctNodes() throws Exception { 
//TODO: Test goes here...
    MyPath path1 = new MyPath(1,2,3,4);
    HashMap<Integer, Integer> expected;

    //assertEquals(expected, path1.getDistinctNodes());
} 

/** 
* 
* Method: equals(Object obj) 
* 
*/ 
@Test
public void testEquals() throws Exception { 
//TODO: Test goes here...
    MyPath path1 = new MyPath(1,2,3,4);
    MyPath path2 = new MyPath(1,2,3,4);

    assertEquals(true, path1.equals(path2));
} 

/** 
* 
* Method: isValid() 
* 
*/ 
@Test
public void testIsValid() throws Exception { 
//TODO: Test goes here...
    MyPath path1 = new MyPath(1,2);
    MyPath path2 = new MyPath();

    assertEquals(true, path1.isValid());
    assertEquals(false, path2.isValid());
} 

/** 
* 
* Method: iterator() 
* 
*/ 
@Test
public void testIterator() throws Exception { 
//TODO: Test goes here...
    MyPath path1 = new MyPath(1,1,2,3,1);
    Iterator<Integer> iterator = path1.iterator();

    while (iterator.hasNext()) {
        System.out.println(iterator.next());
    }
} 

/** 
* 
* Method: compareTo(Path p) 
* 
*/ 
@Test
public void testCompareTo() throws Exception { 
//TODO: Test goes here...
    MyPath path1 = new MyPath(1,2,3,4);
    MyPath path2 = new MyPath(1,2,3,4,5);

    assertEquals(-1, path1.compareTo(path2));
} 

/** 
* 
* Method: hashCode() 
* 
*/ 
@Test
public void testHashCode() throws Exception { 
//TODO: Test goes here...
    MyPath path1 = new MyPath(1,2,3,4);
    MyPath path2 = new MyPath(1,2,3,4);

    assertEquals(path1.hashCode(), path2.hashCode());
}


    @org.testng.annotations.Test
    public void testSize1() {
    }

    @org.testng.annotations.Test
    public void testGetNode1() {
    }

    @org.testng.annotations.Test
    public void testContainsNode1() {
    }

    @org.testng.annotations.Test
    public void testGetDistinctNodeCount1() {
    }

    @org.testng.annotations.Test
    public void testGetDistinctNodes1() {
    }

    @org.testng.annotations.Test
    public void testEquals1() {
    }

    @org.testng.annotations.Test
    public void testIsValid1() {
    }

    @org.testng.annotations.Test
    public void testIterator1() {
    }

    @org.testng.annotations.Test
    public void testCompareTo1() {
    }
}
