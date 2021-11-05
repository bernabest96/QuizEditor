package junit.customqueue;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import view.CustomQueue;
import view.ICustomQueue;

/**
 * Test delle funzionalità della classe.
 * ATTENZIONE: metodi size(), maxSize(), getArray() si considerano corretti e quindi da non testare.
 * @author berna
 *
 */
@RunWith(Parameterized.class)
public class CustomQueueFunctionalityTest {
	
	private ICustomQueue<String> q;
	
	private String[] inputStrings;
	private String[] expectedStrings;
	private int max_dim;
	private String toStr;
	private boolean hasReachedMaxSize;
	
	public CustomQueueFunctionalityTest(String[] inputStrings, String[] expectedStrings, int max_dim, String toStr, boolean hasReachedMaxSize) {
		this.inputStrings = inputStrings;
		this.expectedStrings = expectedStrings;
		this.max_dim = max_dim;
		this.toStr = toStr;
		this.hasReachedMaxSize = hasReachedMaxSize;
	}
	
	@Parameters
	public static Collection<Object[]> data() {
        Object[][] data = new Object[][] { 
        	{ new String[]{}, new String[]{}, 1, "", false},
        	{ new String[]{"s1"}, new String[]{"s1"}, 1, "s1\r\n", true},
        	{ new String[]{"s1", "s2", "s3"}, new String[]{"s3"}, 1, "s3\r\n", true}, 
        	{ new String[]{"s1", "s2", "s3"}, new String[]{"s1", "s2", "s3"}, 5, "s1\r\ns2\r\ns3\r\n", false}, 
        	{ new String[]{"s1", "s2", "s3", "s4", "s5"}, new String[]{"s1", "s2", "s3", "s4", "s5"}, 5 , "s1\r\ns2\r\ns3\r\ns4\r\ns5\r\n", true}, 
        	{ new String[]{"s1", "s2", "s3", "s4", "s5", "s6", "s7"}, new String[]{"s3", "s4", "s5", "s6", "s7"}, 5 , "s3\r\ns4\r\ns5\r\ns6\r\ns7\r\n", true},
        	{ new String[]{"s1", "s2", "s3"}, new String[]{"s1", "s2", "s3"}, 7, "s1\r\ns2\r\ns3\r\n", false},
        	{ new String[]{"s1", "s2", "s3", "s4", "s5", "s6", "s7"}, new String[]{"s1", "s2", "s3", "s4", "s5", "s6", "s7"}, 7, "s1\r\ns2\r\ns3\r\ns4\r\ns5\r\ns6\r\ns7\r\n", true},
        	{ new String[]{"s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8"}, new String[]{"s2", "s3", "s4", "s5", "s6", "s7", "s8"}, 7, "s2\r\ns3\r\ns4\r\ns5\r\ns6\r\ns7\r\ns8\r\n", false}
        	};
        return Arrays.asList(data);
    }
	
	@Before
	public void setup() {
		//System.out.println("Setup");
		q = new CustomQueue<String>(max_dim);
		for (String s : inputStrings) {
			q.enqueue(s);
		}
	}
	
	@Test
	public void insertQueue() {
		assertTrue(q.size() <= max_dim);
		assertArrayEquals(expectedStrings, q.getArray());
	}
	
	@Test
	public void isEmptyTest() {
		//nuovo oggetto vuoto
		CustomQueue<String> q2 = new CustomQueue<String>(max_dim);
		assertTrue("q2.size == 0", q2.size() == 0);
		assertTrue(q2.isEmpty());
	}
	
	@Test
	public void resetTest() {
		q.reset();
		assertTrue(q.isEmpty());
	}
	
	@Test
	public void toStringTest() {
		assertEquals(toStr, q.toString());
	}
	
	public void hasReachedTest() {
		assertTrue(q.hasReachedMaxsize() == hasReachedMaxSize);
	}
		
}
