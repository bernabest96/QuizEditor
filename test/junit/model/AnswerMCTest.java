package junit.model;

import static org.junit.Assert.assertEquals;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import model.AnswerMC;

public class AnswerMCTest {
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest01() {
		AnswerMC a = new AnswerMC(null, "question", "A", "B", "C", "D", "A", "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void contructorTest02() {
		AnswerMC a = new AnswerMC("", "question", "A", "B", "C", "D", "A", "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void contructorTest03() {
		AnswerMC a = new AnswerMC("category", "question", "A", "B", "C", "D", "A", "");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest04() {
		AnswerMC a = new AnswerMC("category", "question", "A", "B", "C", "D", "A", null);
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest05() {
		AnswerMC a = new AnswerMC("category", "question", "A", "B", "C", "D", "diversoDaABCD", "null");
	}
	
	@Test
	public void equalsTest01() {
		AnswerMC a1 = new AnswerMC("category", "question01", "Ada", "Bdasd", "C", "D", "A", "sad");
		AnswerMC a2 = new AnswerMC("category", "question02", "Adasd", "Bdad", "C", "D", "B", "sad");
		assertTrue(!a1.equals(a2));
	}
	
	@Test
	public void equalsTest02() {
		AnswerMC a1 = new AnswerMC("category01", "question", "A", "B", "C", "D", "A", "sad");
		AnswerMC a2 = new AnswerMC("category02", "question", "A", "B", "C", "D", "B", "sad");
		assertTrue(!a1.equals(a2));
	}
	
	@Test
	public void equalsTest03() {
		AnswerMC a1 = new AnswerMC("category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		AnswerMC a2 = new AnswerMC("category", "question", "A", "B", "C", "D", "B", "sad");
		assertTrue(a1.equals(a2));
	}
	
	@Test
	public void equalsTest04() {
		AnswerMC a1 = new AnswerMC("category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		AnswerMC a2 = null;
		assertFalse(a1.equals(a2));
		assertFalse(a1.equals(new String("stringa")));
	}
	
	@Test
	public void toStringTest01() {
		AnswerMC a1 = new AnswerMC("category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String str = "\"category\",\"question\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		assertEquals(str, a1.toString());
	}
	
	@Test
	public void toStringTest02() {
		AnswerMC a1 = new AnswerMC("category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String str = "\"category\", \"question\", \"Ax\", \"Bx\", \"Cx\", \"Dx\", \"A\", \"sad\"";
		assertNotEquals(str, a1.toString());
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void isCorrectTest01() {
		AnswerMC a1 = new AnswerMC("category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		a1.isCorrect(null);
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void isCorrectTest02() {
		AnswerMC a1 = new AnswerMC("category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		a1.isCorrect("");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void isCorrectTest03() {
		AnswerMC a1 = new AnswerMC("category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		a1.isCorrect("risposta");
	}
	
	@Test
	public void isCorrectTest04() {
		AnswerMC a1 = new AnswerMC("category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		assertTrue(a1.isCorrect("A"));
	}
	
	@Test
	public void isCorrectTest05() {
		AnswerMC a1 = new AnswerMC("category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		assertFalse(a1.isCorrect("B"));
	}
}
