import org.junit.Test;
import org.junit.Before; 
import org.junit.After;
import util.MyPath;
import util.MyRailwaySystem;

/** 
* util.MyRailwaySystem Tester.
* 
* @author <Authors name> 
* @since <pre>���� 14, 2019</pre> 
* @version 1.0 
*/ 
public class MyRailwaySystemTest { 

@Before
public void before() throws Exception { 
} 

@After
public void after() throws Exception { 
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
* Method: addPath(Path path) 
* 
*/ 
@Test
public void testAddPath() throws Exception { 
//TODO: Test goes here... 
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
* Method: containsNode(int nodeId) 
* 
*/ 
@Test
public void testContainsNode() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: containsEdge(int fromNodeId, int toNodeId) 
* 
*/ 
@Test
public void testContainsEdge() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: isConnected(int fromNodeId, int toNodeId) 
* 
*/ 
@Test
public void testIsConnected() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getShortestPathLength(int fromNodeId, int toNodeId) 
* 
*/ 
@Test
public void testGetShortestPathLength() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getLeastTicketPrice(int fromNodeId, int toNodeId) 
* 
*/ 
@Test
public void testGetLeastTicketPrice() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getLeastTransferCount(int fromNodeId, int toNodeId) 
* 
*/ 
@Test
public void testGetLeastTransferCount() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getLeastUnpleasantValue(int fromNodeId, int toNodeId) 
* 
*/ 
@Test
public void testGetLeastUnpleasantValue() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getConnectedBlockCount() 
* 
*/ 
@Test
public void testGetConnectedBlockCount() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: containsPathSequence(Path[] pseq) 
* 
*/ 
@Test
public void testContainsPathSequence() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: isConnectedInPathSequence(Path[] pseq, int fromNodeId, int toNodeId) 
* 
*/ 
@Test
public void testIsConnectedInPathSequence() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getTicketPrice(Path[] pseq, int fromNodeId, int toNodeId) 
* 
*/ 
@Test
public void testGetTicketPrice() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getUnpleasantValue(Path path, int[] idx) 
* 
*/ 
@Test
public void testGetUnpleasantValueForPathIdx() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getUnpleasantValue(Path path, int fromIndex, int toIndex) 
* 
*/ 
@Test
public void testGetUnpleasantValueForPathFromIndexToIndex() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getUnpleasantValue(Path[] pseq, int fromNodeId, int toNodeId) 
* 
*/ 
@Test
public void testGetUnpleasantValueForPseqFromNodeIdToNodeId() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: print() 
* 
*/ 
@Test
public void testPrint() throws Exception { 
//TODO: Test goes here...
    MyRailwaySystem railwaySystem = new MyRailwaySystem();
    MyPath path1 = new MyPath(1000, 1001);
    MyPath path2 = new MyPath(1001, 1002);

    railwaySystem.addPath(path1);
    railwaySystem.addPath(path2);

} 


/** 
* 
* Method: initWeightMatrix() 
* 
*/ 
@Test
public void testInitWeightMatrix() throws Exception { 
//TODO: Test goes here... 
/* 
try { 
   Method method = util.MyRailwaySystem.getClass().getMethod("initWeightMatrix");
   method.setAccessible(true); 
   method.invoke(<Object>, <Parameters>); 
} catch(NoSuchMethodException e) { 
} catch(IllegalAccessException e) { 
} catch(InvocationTargetException e) { 
} 
*/ 
} 

/** 
* 
* Method: splitNode(Integer node, Integer pathId) 
* 
*/ 
@Test
public void testSplitNode() throws Exception { 
//TODO: Test goes here... 
/* 
try { 
   Method method = util.MyRailwaySystem.getClass().getMethod("splitNode", Integer.class, Integer.class);
   method.setAccessible(true); 
   method.invoke(<Object>, <Parameters>); 
} catch(NoSuchMethodException e) { 
} catch(IllegalAccessException e) { 
} catch(InvocationTargetException e) { 
} 
*/ 
} 

/** 
* 
* Method: addMyPath(Integer pathId, util.MyPath myPath)
* 
*/ 
@Test
public void testAddMyPath() throws Exception { 
//TODO: Test goes here... 
/* 
try { 
   Method method = util.MyRailwaySystem.getClass().getMethod("addMyPath", Integer.class, util.MyPath.class);
   method.setAccessible(true); 
   method.invoke(<Object>, <Parameters>); 
} catch(NoSuchMethodException e) { 
} catch(IllegalAccessException e) { 
} catch(InvocationTargetException e) { 
} 
*/ 
} 

} 
