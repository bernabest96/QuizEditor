package junit.customqueue;

import static org.junit.Assert.*;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import view.CustomQueue;

public class CustomQueueStatementTest {

	CustomQueue<String> q;
	
	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Test
	public void enqueue01() {
		q = new CustomQueue<String>(1);
		q.enqueue("s1");
		q.enqueue("s2");
		assertArrayEquals(new String[] {"s2"},  q.getArray());
	}

}
