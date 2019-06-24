package homework;

import org.junit.Assert;
import org.junit.Test;
import org.junit.Before; 
import org.junit.After;
import org.junit.Assert.*;

/** 
* MyPathContainer Tester. 
* 
* @author <Authors name> 
* @since <pre>ËÄÔÂ 29, 2019</pre> 
* @version 1.0 
*/ 
public class MyPathContainerTest { 
    MyPathContainer myPathContainer = new MyPathContainer();

    public MyPathContainerTest() {
        myPathContainer.addPath(new MyPath(1,2,3,4));
        myPathContainer.addPath(new MyPath(1,2,2,3));
        myPathContainer.addPath(new MyPath(4,3,2,1));

    }

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
    int size = 3;
    myPathContainer.addPath(new MyPath(1,2,3,4));

    Assert.assertEquals(size, myPathContainer.size());
} 

/** 
* 
* Method: containsPath(Path path) 
* 
*/ 
@Test
public void testContainsPath() throws Exception { 
//TODO: Test goes here...
    MyPath path = new MyPath(1,2,2,3);

    Assert.assertEquals(true, myPathContainer.containsPath(path));
} 

/** 
* 
* Method: containsPathId(int pathId) 
* 
*/ 
@Test
public void testContainsPathId() throws Exception { 
//TODO: Test goes here...
    myPathContainer.removePathById(2);
    Assert.assertEquals(true, myPathContainer.containsPathId(3));
} 

/** 
* 
* Method: getPathById(int pathId) 
* 
*/ 
@Test
public void testGetPathById() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getPathId(Path path) 
* 
*/ 
@Test
public void testGetPathId() throws Exception { 
//TODO: Test goes here...
    MyPath path = new MyPath(1,2,2,3);

    Assert.assertEquals(2, myPathContainer.getPathId(path));
} 

/** 
* 
* Method: addPath(Path path) 
* 
*/ 
@Test
public void testAddPath() throws Exception { 
//TODO: Test goes here...
    MyPath path = new MyPath(1,2,2,3);
    MyPath path2 = new MyPath(1,2,2,3,2);
    Assert.assertEquals(2, myPathContainer.addPath(path));
    Assert.assertEquals(4, myPathContainer.addPath(path2));
} 

/** 
* 
* Method: removePath(Path path) 
* 
*/ 
@Test
public void testRemovePath() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: removePathById(int pathId) 
* 
*/ 
@Test
public void testRemovePathById() throws Exception { 
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
    Assert.assertEquals(4, myPathContainer.getDistinctNodeCount());
} 


/** 
* 
* Method: updDistNodeCnt() 
* 
*/ 
@Test
public void testUpdDistNodeCnt() throws Exception { 
//TODO: Test goes here... 
/* 
try { 
   Method method = MyPathContainer.getClass().getMethod("updDistNodeCnt"); 
   method.setAccessible(true); 
   method.invoke(<Object>, <Parameters>); 
} catch(NoSuchMethodException e) { 
} catch(IllegalAccessException e) { 
} catch(InvocationTargetException e) { 
} 
*/ 
} 

} 
