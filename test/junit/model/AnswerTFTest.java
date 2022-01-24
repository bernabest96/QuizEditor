package junit.model;

import static org.junit.Assert.*;

import org.junit.Test;

import model.AnswerMC;
import model.AnswerTF;

public class AnswerTFTest {

	private AnswerTF a;
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest01() {
		AnswerTF a = new AnswerTF(0, null, "question", true, "caption");
	}
	//null values
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest012() {
		AnswerTF a = new AnswerTF(0, "category", null, true, "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest05() {
		AnswerTF a = new AnswerTF(0, "category", "question", false, null);
	}
	
	//empty values
	@Test(expected = IllegalArgumentException.class)
	public void contructorTest02() {
		AnswerTF a = new AnswerTF(0, "", "question", true, "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest03() {
		AnswerTF a = new AnswerTF(0, "category", "", true, "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest04() {
		AnswerTF a = new AnswerTF(0, "category", "question", false, "");
	}
	//negative line
	@Test(expected = IllegalArgumentException.class)
	public void constructorTest06() {
		AnswerTF a = new AnswerTF(-1, "category", "question", true, "caption");
	}
	
	@Test
	public void equalsTest01() {
		AnswerTF a1 = new AnswerTF(0, "category", "question01", true, "sad");
		AnswerTF a2 = new AnswerTF(0, "category", "question02", false, "sad");
		assertTrue(!a1.equals(a2));
	}
	
	@Test
	public void equalsTest02() {
		AnswerTF a1 = new AnswerTF(0, "category01", "question", true, "sad");
		AnswerTF a2 = new AnswerTF(0, "category02", "question", true, "sad");
		assertTrue(!a1.equals(a2));
	}
	
	@Test
	public void equalsTest03() {
		AnswerTF a1 = new AnswerTF(0, "category", "question", true, "sad");
		AnswerTF a2 = new AnswerTF(0, "category", "question", false, "sad");
		assertTrue(a1.equals(a2));
	}
	
	@Test
	public void equalsTest04() {
		AnswerTF a1 = new AnswerTF(0, "category", "question", true, "sad");
		AnswerTF a2 = null;
		assertFalse(a1.equals(a2));
		assertFalse(a1.equals(new String("stringa")));
	}
	
	@Test
	public void toStringToFileTest01() {
		AnswerTF a1 = new AnswerTF(0, "category", "question", false, "sad");
		String str = "\"category\",\"question\",\"f\",\"sad\"";
		assertEquals(str, a1.toStringToFile());
		AnswerTF a2 = new AnswerTF(0, "category", "question", true, "sad");
		String str2 = "\"category\",\"question\",\"t\",\"sad\"";
		assertEquals(str2, a2.toStringToFile());
	}
	
	@Test
	public void toStringToFileTest02() {
		AnswerTF a1 = new AnswerTF(0, "category", "question", false, "sad");
		String str = "\"category\", \"question\", \"f\", \"sad\"";
		assertNotEquals(str, a1.toStringToFile());
	}
	
	@Test
	public void toStringToFileTest03() {
		AnswerTF a1 = new AnswerTF(0, "category", "quanto vale \"x^2\"?", true, "sad");
		String strDashQuote = "\"category\",\"quanto vale \\\"x^2\\\"?\",\"t\",\"sad\"";
		String strQuote = "\"category\",\"quanto vale \"x^2\"?\",\"t\",\"sad\"";
		assertEquals(strDashQuote, a1.toStringToFile());
		assertNotEquals(strQuote, a1.toStringToFile());
	}
	
	@Test
	public void toStringToFileTest04() {
		AnswerTF a1 = new AnswerTF(0, "category", "qui separo " + System.lineSeparator() + " qua è andato a capo", true, "sad");
		String strDashLineSep = "\"category\",\"qui separo \\r\\n qua è andato a capo\",\"t\",\"sad\"";
		String strLineSep = "\"category\",\"qui separo " + System.lineSeparator() + " qua è andato a capo\",\"t\",\"sad\"";
		assertEquals(strDashLineSep, a1.toStringToFile());
		assertNotEquals(strLineSep, a1.toStringToFile());
	}
	
	@Test
	public void toStringWithLineTest01() {
		AnswerTF a1 = new AnswerTF(5, "category", "question", true, "sad");
		String str = "\"category\",\"question\",\"t\",\"sad\"";
		assertNotEquals(str, a1.toStringWithLine());
	}
	
	@Test
	public void toStringWithLineTest02() {
		AnswerTF a2 = new AnswerTF(5, "category", "question", false, "sad");
		String str2 = "Line 5: \"category\",\"question\",\"f\",\"sad\"";
		//fallisce perche ci sono gli spazi
		assertEquals(str2, a2.toStringWithLine());
	}
	
	@Test
	public void toStringWithLineTest03() {
		AnswerTF a1 = new AnswerTF(0, "category", "question", true, "sad");
		String str = "Line 0: \"category\",\"question\",\"t\",\"sad\"";
		assertNotEquals(str, a1.toStringWithLine());
		String str2 = "Nessuna linea del file è associata al quiz";
		assertEquals(str2, a1.toStringWithLine());
	}
	
	@Test
	public void toStringWithLineTest04() {
		AnswerTF a1 = new AnswerTF(6, "category", "qui separo \\r\\n qua è andato a capo", true, "sad");
		String str = "Line 0: \"category\",\"question\",\"t\",\"sad\"";
		String strDashLineSep = "Line 6: \"category\",\"qui separo \\r\\n qua è andato a capo\",\"t\",\"sad\"";
		String strLineSep = "Line 6: \"category\",\"qui separo " + System.lineSeparator() + " qua è andato a capo\",\"t\",\"sad\"";
		assertEquals(strDashLineSep, a1.toStringWithLine());
		assertNotEquals(strLineSep, a1.toStringWithLine());
	}
	
	@Test
	public void isCorrectTest01() {
		AnswerTF a1 = new AnswerTF(0, "category", "question", true, "sad");
		assertTrue(a1.isCorrect(true));
	}
	
	@Test
	public void isCorrectTest02() {
		AnswerTF a1 = new AnswerTF(0, "category", "question", true, "sad");
		assertFalse(a1.isCorrect(false));
	}

}
