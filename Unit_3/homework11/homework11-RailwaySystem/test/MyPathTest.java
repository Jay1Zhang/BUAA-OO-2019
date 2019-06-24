import com.oocourse.specs3.models.Path;
import org.junit.Assert;
import org.junit.Test;
import org.junit.Before; 
import org.junit.After;
import util.MyPath;

/** 
* util.MyPath Tester.
* 
* @author <Authors name> 
* @since <pre>���� 12, 2019</pre> 
* @version 1.0 
*/ 
public class MyPathTest { 

@Before
public void before() throws Exception { 
} 

@After
public void after() throws Exception { 
} 

/** 
* 
* Method: size() 
* 
*/ 
@Test
public void testSize() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getNode(int index) 
* 
*/ 
@Test
public void testGetNode() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: containsNode(int node) 
* 
*/ 
@Test
public void testContainsNode() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getDistinctNodeCount() 
* 
*/ 
@Test
public void testGetDistinctNodeCount() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getNodesList() 
* 
*/ 
@Test
public void testGetNodesList() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getDistinctNodesSet() 
* 
*/ 
@Test
public void testGetDistinctNodesSet() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: equals(Object obj) 
* 
*/ 
@Test
public void testEquals() throws Exception { 
//TODO: Test goes here...
    Path path1 = new MyPath(1,2,3);
    Path path2 = new MyPath(1,2,3);
    Path path3 = new MyPath(3,2,1);

    Assert.assertTrue(path1.equals(path1));
    Assert.assertTrue(path1.equals(path2));
    Assert.assertFalse(path1.equals(path3));
} 

/** 
* 
* Method: isValid() 
* 
*/ 
@Test
public void testIsValid() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getUnpleasantValue(int nodeId) 
* 
*/ 
@Test
public void testGetUnpleasantValue() throws Exception { 
//TODO: Test goes here...
    /*
    HashMap<Integer, Integer> map = new HashMap<>();
    map.put(1, 1);
    Assert.assertEquals(Integer.valueOf(1), map.get(Integer.valueOf(1)));
    map.get(Integer.valueOf(1))++;
    */

    /*
    util.MyPath myPath = new util.MyPath(2, 3, 5);

    Assert.assertEquals(16, myPath.getUnpleasantValue(2));
    Assert.assertEquals(64, myPath.getUnpleasantValue(3));
    Assert.assertEquals(0, myPath.getUnpleasantValue(1));
    */
} 

/** 
* 
* Method: iterator() 
* 
*/ 
@Test
public void testIterator() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: compareTo(Path p) 
* 
*/ 
@Test
public void testCompareTo() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: hashCode() 
* 
*/ 
@Test
public void testHashCode() throws Exception { 
//TODO: Test goes here... 
} 


} 
