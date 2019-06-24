package test.base; 

import base.Node;
import org.junit.Assert;
import org.junit.Test;
import org.junit.Before; 
import org.junit.After; 

/** 
* Node Tester. 
* 
* @author <Authors name> 
* @since <pre>���� 18, 2019</pre> 
* @version 1.0 
*/ 
public class NodeTest { 

@Before
public void before() throws Exception { 
} 

@After
public void after() throws Exception { 
} 

/** 
* 
* Method: getNodeId() 
* 
*/ 
@Test
public void testGetNodeId() throws Exception { 
//TODO: Test goes here... 
} 

/** 
* 
* Method: getPathId() 
* 
*/ 
@Test
public void testGetPathId() throws Exception { 
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
} 

/** 
* 
* Method: hashCode() 
* 
*/ 
@Test
public void testHashCode() throws Exception { 
//TODO: Test goes here...
    Node node1 = new Node(1, 1);
    Node node2 = new Node(1, 1);

    Assert.assertEquals(node1.hashCode(), node2.hashCode());
    Assert.assertTrue(node1.equals(node2));

} 


} 
