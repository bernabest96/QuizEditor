package junit.model;

import static org.junit.Assert.*;

import org.junit.Test;

import model.AnswerMC;
import model.AnswerTF;

public class AnswerTFTest {

	private AnswerTF a;
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest01() {
		AnswerTF a = new AnswerTF(null, "question", true, "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest012() {
		AnswerTF a = new AnswerTF("category", null, true, "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void contructorTest02() {
		AnswerTF a = new AnswerTF("", "question", true, "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void contructorTest03() {
		AnswerTF a = new AnswerTF("category", "question", false, "");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest04() {
		AnswerTF a = new AnswerTF("category", "question", false, null);
	}
	
	@Test
	public void equalsTest01() {
		AnswerTF a1 = new AnswerTF("category", "question01", true, "sad");
		AnswerTF a2 = new AnswerTF("category", "question02", false, "sad");
		assertTrue(!a1.equals(a2));
	}
	
	@Test
	public void equalsTest02() {
		AnswerTF a1 = new AnswerTF("category01", "question", true, "sad");
		AnswerTF a2 = new AnswerTF("category02", "question", true, "sad");
		assertTrue(!a1.equals(a2));
	}
	
	@Test
	public void equalsTest03() {
		AnswerTF a1 = new AnswerTF("category", "question", true, "sad");
		AnswerTF a2 = new AnswerTF("category", "question", false, "sad");
		assertTrue(a1.equals(a2));
	}
	
	@Test
	public void equalsTest04() {
		AnswerTF a1 = new AnswerTF("category", "question", true, "sad");
		AnswerTF a2 = null;
		assertFalse(a1.equals(a2));
		assertFalse(a1.equals(new String("stringa")));
	}
	
	@Test
	public void toStringTest01() {
		AnswerTF a1 = new AnswerTF("category", "question", false, "sad");
		String str = "\"category\",\"question\",\"f\",\"sad\"";
		assertEquals(str, a1.toString());
	}
	
	@Test
	public void toStringTest02() {
		AnswerTF a1 = new AnswerTF("category", "question", true, "sad");
		String str = "\"category\",\"question\",\"t\",\"sad\"";
		assertEquals(str, a1.toString());
	}
	
	@Test
	public void toStringTest03() {
		AnswerTF a1 = new AnswerTF("category", "question", false, "sad");
		String str = "\"category\", \"question\", \"f\", \"sad\"";
		assertNotEquals(str, a1.toString());
	}
	
	@Test
	public void isCorrectTest01() {
		AnswerTF a1 = new AnswerTF("category", "question", true, "sad");
		assertTrue(a1.isCorrect(true));
	}
	
	@Test
	public void isCorrectTest02() {
		AnswerTF a1 = new AnswerTF("category", "question", true, "sad");
		assertFalse(a1.isCorrect(false));
	}

}
