package junit.model;

import static org.junit.Assert.assertEquals;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import model.AnswerMC;
import model.AnswerTF;

public class AnswerMCTest {
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest01() {
		AnswerMC a = new AnswerMC(0, null, "question", "A", "B", "C", "D", "A", "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void contructorTest02() {
		AnswerMC a = new AnswerMC(0, "", "question", "A", "B", "C", "D", "A", "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void contructorTest03() {
		AnswerMC a = new AnswerMC(0, "category", "question", "A", "B", "C", "D", "A", "");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest04() {
		AnswerMC a = new AnswerMC(0, "category", "question", "A", "B", "C", "D", "A", null);
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest05() {
		AnswerMC a = new AnswerMC(0, "category", "question", "A", "B", "C", "D", "diversoDaABCD", "null");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest06() {
		AnswerMC a = new AnswerMC(-1, "category", "question", "A", "B", "C", "D", "diversoDaABCD", "null");
	}
	
	@Test
	public void equalsTest01() {
		AnswerMC a1 = new AnswerMC(0, "category", "question01", "Ada", "Bdasd", "C", "D", "A", "sad");
		AnswerMC a2 = new AnswerMC(0, "category", "question02", "Adasd", "Bdad", "C", "D", "B", "sad");
		assertTrue(!a1.equals(a2));
	}
	
	@Test
	public void equalsTest02() {
		AnswerMC a1 = new AnswerMC(0, "category01", "question", "A", "B", "C", "D", "A", "sad");
		AnswerMC a2 = new AnswerMC(0, "category02", "question", "A", "B", "C", "D", "B", "sad");
		assertTrue(!a1.equals(a2));
	}
	
	@Test
	public void equalsTest03() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		AnswerMC a2 = new AnswerMC(0, "category", "question", "A", "B", "C", "D", "B", "sad");
		assertTrue(a1.equals(a2));
	}
	
	@Test
	public void equalsTest04() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		AnswerMC a2 = null;
		assertFalse(a1.equals(a2));
		assertFalse(a1.equals(new String("stringa")));
	}
	
	@Test
	public void toStringToFileTest01() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String str = "\"category\",\"question\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		assertEquals(str, a1.toStringToFile());
	}
	
	@Test
	public void toStringToFileTest02() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String str = "\"category\", \"question\", \"Ax\", \"Bx\", \"Cx\", \"Dx\", \"A\", \"sad\"";
		//fallisce perche ci sono gli spazi
		assertNotEquals(str, a1.toStringToFile());
	}
	
	@Test
	public void toStringToFileTest03() {
		AnswerMC a1 = new AnswerMC(0, "category", "quanto vale \"x^2\"?", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String strDashQuote = "\"category\",\"quanto vale \\\"x^2\\\"?\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		String strQuote = "\"category\",\"quanto vale \"x^2\"?\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		assertEquals(strDashQuote, a1.toStringToFile());
		assertNotEquals(strQuote, a1.toStringToFile());
	}
	
	@Test
	public void toStringToFileTest04() {
		AnswerMC a1 = new AnswerMC(0, "category", "qui separo " + System.lineSeparator() + " qua è andato a capo", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String strDashLineSep = "\"category\",\"qui separo \\r\\n qua è andato a capo\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		String strLineSep = "\"category\",\"qui separo " + System.lineSeparator() + " qua è andato a capo\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		assertEquals(strDashLineSep, a1.toStringToFile());
		assertNotEquals(strLineSep, a1.toStringToFile());
	}
	
	@Test
	public void toStringWithLineTest01() {
		AnswerMC a1 = new AnswerMC(5, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String str = "\"category\",\"question\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		assertNotEquals(str, a1.toStringWithLine());
	}
	
	@Test
	public void toStringWithLineTest02() {
		AnswerMC a2 = new AnswerMC(5, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String str2 = "Line 5: \"category\",\"question\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		//fallisce perche ci sono gli spazi
		assertEquals(str2, a2.toStringWithLine());
	}
	
	@Test
	public void toStringWithLineTest03() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String str = "Line 0: \"category\",\"question\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		assertNotEquals(str, a1.toStringWithLine());
		String str2 = "Nessuna linea del file è associata al quiz";
		assertEquals(str2, a1.toStringWithLine());
	}
	
	@Test
	public void toStringWithLineTest04() {
		AnswerMC a1 = new AnswerMC(6, "category", "qui separo \\r\\n qua è andato a capo", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		String strDashLineSep = "Line 6: \"category\",\"qui separo \\r\\n qua è andato a capo\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		String strLineSep = "Line 6: \"category\",\"qui separo " + System.lineSeparator() + " qua è andato a capo\",\"Ax\",\"Bx\",\"Cx\",\"Dx\",\"A\",\"sad\"";
		assertEquals(strDashLineSep, a1.toStringWithLine());
		assertNotEquals(strLineSep, a1.toStringWithLine());
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void isCorrectTest01() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		a1.isCorrect(null);
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void isCorrectTest02() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		a1.isCorrect("");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void isCorrectTest03() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		a1.isCorrect("risposta");
	}
	
	@Test
	public void isCorrectTest04() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		assertTrue(a1.isCorrect("A"));
	}
	
	@Test
	public void isCorrectTest05() {
		AnswerMC a1 = new AnswerMC(0, "category", "question", "Ax", "Bx", "Cx", "Dx", "A", "sad");
		assertFalse(a1.isCorrect("B"));
	}
}
