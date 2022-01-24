package junit.customqueue;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import view.CustomQueue;
import view.ICustomQueue;

public class CustomQueueCapacityTest {
	private ICustomQueue q;
	private int max_capacity = 10;
	
	public CustomQueueCapacityTest() {
		q = new CustomQueue(max_capacity);
	}
	
	
	@Test(expected = IllegalArgumentException.class)
	public void CapacityTest01() {
		new CustomQueue(-1);	
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void CapacityTest02() {
		new CustomQueue(0);
	}
	
	@Test()
	public void CapacityTest03() {
		assertEquals(max_capacity, q.maxSize());	
	}
	
	@Test
	public void CapacityTest04() {
		assertEquals(0, q.size());
	}
	
	@Test
	public void CapacityTest05() {
		assertTrue(q.isEmpty());
	}
	
}
