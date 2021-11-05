package junit.model;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import model.AnswerMC;

@RunWith(Parameterized.class)
public class AnswerMCTestSTATEMENTBRANCHLOOP {
	
	private String[] strInp;
	
	@Parameters
	public static Collection<Object[]> data(){
		Object[][] data = new Object[][] {
			{new String[] {null, "question", "A", "B", "C", "D", "A", "caption" }},
			{new String[] {"category", null, "A", "B", "C", "D", "A", "caption" }},
			{new String[] {"category", "question", null, "B", "C", "D", "A", "caption" }},
			{new String[] {"category", "question", "A", null, "C", "D", "A", "caption" }},
			{new String[] {"category", "question", "A", "B", null, "D", "A", "caption" }},
			{new String[] {"category", "question", "A", "B", "C", null, "A", "caption" }},
			{new String[] {"category", "question", "A", "B", "C", "D", null, "caption" }},
			{new String[] {"category", "question", "A", "B", "C", "D", "A", null }},
			{new String[] {"", "question", "A", "B", "C", "D", "A", "caption" }},
			{new String[] {"category", "", "A", "B", "C", "D", "A", "caption" }},
			{new String[] {"category", "question", "", "B", "C", "D", "A", "caption" }},
			{new String[] {"category", "question", "A", "", "C", "D", "A", "caption" }},
			{new String[] {"category", "question", "A", "B", "", "D", "A", "caption" }},
			{new String[] {"category", "question", "A", "B", "C", "", "A", "caption" }},
			{new String[] {"category", "question", "A", "B", "C", "D", "", "caption" }},
			{new String[] {"category", "question", "A", "B", "C", "D", "A", "" }},
//			{new String[] {"category", "question", "A", "B", "C", "D", "A", "caption" }}
		};
		return Arrays.asList(data);
	}
	
	public AnswerMCTestSTATEMENTBRANCHLOOP(String[] strInp) {
		this.strInp = strInp;
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void stringThrowIllegalMCDCCoverage() {
		AnswerMC a = new AnswerMC(strInp[0], strInp[1], strInp[2], strInp[3], strInp[4], strInp[5], strInp[6], strInp[7]);
	}
	
	@Test
	public void StatementCoverage() {
		AnswerMC a = new AnswerMC("category", "question", "A", "B", "C", "D", "A", "caption");
		assertEquals("category", a.getCategory());
		assertEquals("question", a.getQuestion());
		assertEquals("A", a.getA());
		assertEquals("B", a.getB());
		assertEquals("C", a.getC());
		assertEquals("D", a.getD());
		assertEquals("A", a.getCorrectAnswer());
		assertEquals("caption", a.getCaption());
		String[] ans = new String[] {"A", "B", "C", "D"};
		assertArrayEquals(ans, a.getMCAnswers());
	}

}
