package junit.controller;

import static org.junit.Assert.*;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.hamcrest.CoreMatchers;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Captor;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.Mockito;
import org.mockito.runners.MockitoJUnit44Runner;

import controller.Controller;
import model.AnswerMC;
import model.AnswerTF;
import model.IAnswers;
import model.McModel;
import model.TfModel;
import view.View;

@RunWith(MockitoJUnit44Runner.class)
public class ControllerSearchTest {

	@Captor
	ArgumentCaptor<String> captor;
	@Mock
	McModel mc;
	@Mock
	TfModel tf;
	@Mock
	View v;
	
	@InjectMocks
	Controller c;
	
	@Before
	public void setUp() throws Exception {
		assertNotNull(mc);
		assertNotNull(tf);
		assertNotNull(v);
		c = new Controller(mc, tf, v);
	}
	
	
	
	/**onSearchButtonPressed Testing**/
	
	@Test(expected = IllegalArgumentException.class)
	public void onSearchNullTest() {
		c.onSearchButtonPressed(null);
	}
	
	@SuppressWarnings("deprecation")
	@Test
	public void onSearchFileNotFoundTest01() throws FileNotFoundException, IOException {
//		throw FileNotFoundException for mc
		Mockito.doThrow(new FileNotFoundException()).when(mc).hasKeyWords();
		Mockito.doThrow(new FileNotFoundException()).when(mc).hasWrongLines();
		Mockito.doThrow(new FileNotFoundException()).when(mc).readAnswers("");
		Mockito.when(tf.hasKeyWords()).thenReturn(true);
		Mockito.when(tf.hasWrongLines()).thenReturn(false);
		Mockito.when(tf.readAnswers("")).thenReturn(null);
		assertFalse(c.onSearchButtonPressed(""));
		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
		assertThat(captor.getValue(), CoreMatchers.containsString(Controller.getFileNotFoundMessage()));
	}
	
	
	@SuppressWarnings("deprecation")
	@Test
	public void onSearchFileNotFoundTest02() throws FileNotFoundException, IOException {
//		throw FileNotFoundException for mc
		Mockito.doThrow(new FileNotFoundException()).when(tf).hasKeyWords();
		Mockito.doThrow(new FileNotFoundException()).when(tf).hasWrongLines();
		Mockito.doThrow(new FileNotFoundException()).when(tf).readAnswers("");
		Mockito.when(mc.hasKeyWords()).thenReturn(true);
		Mockito.when(mc.hasWrongLines()).thenReturn(false);
		Mockito.when(mc.readAnswers("")).thenReturn(null);
		assertFalse(c.onSearchButtonPressed(""));
		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
		assertThat(captor.getValue(), CoreMatchers.containsString(Controller.getFileNotFoundMessage()));
	}
	
	@Test
	public void onSearchIOExceptionTest() throws FileNotFoundException, IOException {
		Mockito.doThrow(new IOException()).when(mc).hasKeyWords();
//		Mockito.doThrow(new IOException()).when(tf).readAnswers("");
		assertFalse(c.onSearchButtonPressed(""));
//		Mockito.verify(mc).readAnswers("");
//		Mockito.verify(tf).readAnswers("");
		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
		assertEquals(Controller.getGeneralErrorMessage(), captor.getValue());
	}
	
	//testa quando non ci sono risposte
	@Test
	public void onSearchNothingReturn() throws FileNotFoundException, IOException {
		String category = "cat_a";
		Mockito.when(mc.hasKeyWords()).thenReturn(true);
		Mockito.when(mc.hasWrongLines()).thenReturn(false);
		Mockito.when(tf.hasKeyWords()).thenReturn(true);
		Mockito.when(tf.hasWrongLines()).thenReturn(false);
		Mockito.doReturn(null).when(mc).readAnswers(category);
		Mockito.doReturn(null).when(tf).readAnswers(category);
		assertTrue(c.onSearchButtonPressed(category));
		Mockito.verify(mc).readAnswers(category);
		Mockito.verify(tf).readAnswers(category);
		Mockito.verify(v).displayQuizMessages(Controller.getQuizNotFoundMessage() + category);
	}

	@Test
	public void onSearchReturnOnlyMC() throws FileNotFoundException, IOException {
		String category = "mc_cat";
		//models mocks
		Mockito.doReturn(true).when(mc).hasKeyWords();
		Mockito.doReturn(false).when(mc).hasWrongLines();
		Mockito.doReturn(true).when(tf).hasKeyWords();
		Mockito.doReturn(false).when(tf).hasWrongLines();
		//answerMC
		IAnswers[] ans = new AnswerMC[3];
		ans[0] = new AnswerMC(category, "question01", "A", "B", "C", "D", "A", "caption");
		String ans0 = "\"" + category + "\",\"question01\",\"A\",\"B\",\"C\",\"D\",\"A\",\"caption\"";
		ans[1] = new AnswerMC(category, "question02", "A", "B", "C", "D", "A", "caption");
		String ans1 = "\"" + category + "\",\"question02\",\"A\",\"B\",\"C\",\"D\",\"A\",\"caption\"";
		ans[2] = new AnswerMC(category, "question03", "A", "B", "C", "D", "A", "caption");
		String ans2 = "\"" + category + "\",\"question03\",\"A\",\"B\",\"C\",\"D\",\"A\",\"caption\"";
		
		Mockito.doReturn(ans).when(mc).readAnswers(category);
		Mockito.doReturn(null).when(tf).readAnswers(category);
		assertTrue(c.onSearchButtonPressed(category));
		//verify
		Mockito.verify(mc).readAnswers(category);
		Mockito.verify(tf).readAnswers(category);
		Mockito.verify(v).displayQuizMessages(captor.capture());
		String finalStr = ans0 + System.lineSeparator() + ans1 + System.lineSeparator() + ans2 + System.lineSeparator();
		assertEquals(finalStr, captor.getValue());
	}
	
	@Test
	public void onSearchReturnOnlyTF() throws FileNotFoundException, IOException {
		String category = "tf_cat";
		//models mocks
		Mockito.doReturn(true).when(mc).hasKeyWords();
		Mockito.doReturn(false).when(mc).hasWrongLines();
		Mockito.doReturn(true).when(tf).hasKeyWords();
		Mockito.doReturn(false).when(tf).hasWrongLines();
		//answerTF
		IAnswers[] ans = new AnswerTF[3];
		ans[0] = new AnswerTF(category, "question01", true, "caption");
		String ans0 = "\"" + category + "\",\"question01\",\"t\",\"caption\"";
		ans[1] = new AnswerTF(category, "question02", false, "caption");
		String ans1 = "\"" + category + "\",\"question02\",\"f\",\"caption\"";
		ans[2] = new AnswerTF(category, "question03", true, "caption");
		String ans2 = "\"" + category + "\",\"question03\",\"t\",\"caption\"";
		
		//readAnswers
		Mockito.doReturn(null).when(mc).readAnswers(category);
		Mockito.doReturn(ans).when(tf).readAnswers(category);
		assertTrue(c.onSearchButtonPressed(category));
		//verify
		Mockito.verify(mc).readAnswers(category);
		Mockito.verify(tf).readAnswers(category);
		Mockito.verify(v).displayQuizMessages(captor.capture());
		String finalStr = ans0 + System.lineSeparator() + ans1 + System.lineSeparator() + ans2 + System.lineSeparator();
		assertEquals(finalStr, captor.getValue());
	}
	
	@Test
	public void onSearchReturnMCTF() throws FileNotFoundException, IOException {
		String category = "categ";
		IAnswers[] ansMC = new AnswerMC[3];
		IAnswers[] ansTF = new AnswerTF[3];
		
		//answerMC
		ansMC[0] = new AnswerMC(category, "question01", "A", "B", "C", "D", "A", "caption");
		String ansMC0 = "\"" + category + "\",\"question01\",\"A\",\"B\",\"C\",\"D\",\"A\",\"caption\"";
		ansMC[1] = new AnswerMC(category, "question02", "A", "B", "C", "D", "A", "caption");
		String ansMC1 = "\"" + category + "\",\"question02\",\"A\",\"B\",\"C\",\"D\",\"A\",\"caption\"";
		ansMC[2] = new AnswerMC(category, "question03", "A", "B", "C", "D", "A", "caption");
		String ansMC2 = "\"" + category + "\",\"question03\",\"A\",\"B\",\"C\",\"D\",\"A\",\"caption\"";

		//answerTF
		ansTF[0] = new AnswerTF(category, "question01", true, "caption");
		String ansTF0 = "\"" + category + "\",\"question01\",\"t\",\"caption\"";
		ansTF[1] = new AnswerTF(category, "question02", false, "caption");
		String ansTF1 = "\"" + category + "\",\"question02\",\"f\",\"caption\"";
		ansTF[2] = new AnswerTF(category, "question03", true, "caption");
		String ansTF2 = "\"" + category + "\",\"question03\",\"t\",\"caption\"";
		
		//mockito
		//models mocks
		Mockito.doReturn(true).when(mc).hasKeyWords();
		Mockito.doReturn(false).when(mc).hasWrongLines();
		Mockito.doReturn(true).when(tf).hasKeyWords();
		Mockito.doReturn(false).when(tf).hasWrongLines();
		Mockito.doReturn(ansMC).when(mc).readAnswers(category);
		Mockito.doReturn(ansTF).when(tf).readAnswers(category);
		assertTrue(c.onSearchButtonPressed(category));
		//verify
		Mockito.verify(mc).readAnswers(category);
		Mockito.verify(tf).readAnswers(category);
		Mockito.verify(v).displayQuizMessages(captor.capture());
		String finalStr = ansMC0 + System.lineSeparator() + ansMC1 + System.lineSeparator() + ansMC2 + System.lineSeparator() + 
				ansTF0 + System.lineSeparator() + ansTF1 + System.lineSeparator() + ansTF2 + System.lineSeparator();
		assertEquals(finalStr, captor.getValue());
	}

}
