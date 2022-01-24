package junit.customqueue;

import static org.junit.Assert.*;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import junit.framework.Assert;
import view.CustomQueue;

public class CustomQueueStatementTest {

	CustomQueue q;
	
	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Test
	public void enqueue01() {
		q = new CustomQueue(1);
		q.enqueue("s1");
		q.enqueue("s2");
		assertArrayEquals(new String[] {"s2"},  q.getArray());
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void enqueueNull() {
		q = new CustomQueue(5);
		q.enqueue(null);
	}
	
	@Test
	public void equalsNull() {
		q = new CustomQueue(5);
		assertFalse(q.equals(null));
	}
	
	@Test
	public void equalsWrongClass() {
		q = new CustomQueue(5);
		assertFalse(q.equals("stringa"));
	}
	
	@Test
	public void equalsOK() {
		q = new CustomQueue(2);
		q.enqueue("stringa1");
		q.enqueue("stringa2");
		CustomQueue cq = new CustomQueue(2);
		cq.enqueue("stringa1");
		cq.enqueue("stringa2");
		assertTrue(q.equals(cq));
	}
	
	@Test
	public void hasReachedMaxSide() {
		q = new CustomQueue(1);
		q.enqueue("s1");
		q.enqueue("s2");
		assertTrue(q.hasReachedMaxsize());
	}
	
	@Test
	public void hasNotReachedMaxSide() {
		q = new CustomQueue(5);
		q.enqueue("s1");
		q.enqueue("s2");
		assertFalse(q.hasReachedMaxsize());
	}

}
