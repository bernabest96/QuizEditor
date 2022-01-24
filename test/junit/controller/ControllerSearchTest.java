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
	
	@Test
	public void InsertMChasNotKeysTest() throws FileNotFoundException, IOException {
		Mockito.when(mc.hasKeyWords()).thenReturn(false);
		assertFalse(c.onSearchButtonPressed("category"));
		Mockito.verify(mc).hasKeyWords();
		Mockito.verify(v, Mockito.atLeastOnce()).displayInfoErrorMessages(captor.capture());
		assertEquals(Controller.getSearchAbortMessage(), captor.getValue());
	}
	
	@Test
	public void InsertTFhasNotKeysTest() throws FileNotFoundException, IOException {
		Mockito.when(mc.hasKeyWords()).thenReturn(true);
		Mockito.when(mc.hasWrongLines()).thenReturn(false);
		Mockito.when(tf.hasKeyWords()).thenReturn(false);
		Mockito.when(tf.hasWrongLines()).thenReturn(true);
		assertFalse(c.onSearchButtonPressed("category"));
		Mockito.verify(mc, Mockito.atLeastOnce()).hasKeyWords();
		Mockito.verify(mc).hasWrongLines();
		Mockito.verify(tf, Mockito.atLeastOnce()).hasKeyWords();
		Mockito.verify(v, Mockito.atLeastOnce()).displayInfoErrorMessages(captor.capture());
		assertEquals(Controller.getSearchAbortMessage(), captor.getValue());
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
		String[] str = new String[3];
		ans[0] = new AnswerMC(1, category, "question01", "A", "B", "C", "D", "A", "caption");
		str[0] = ans[0].toStringWithLine();
		ans[1] = new AnswerMC(2, category, "question02", "A", "B", "C", "D", "A", "caption");
		str[1] = ans[1].toStringWithLine();
		ans[2] = new AnswerMC(3, category, "question03", "A", "B", "C", "D", "A", "caption");
		str[2] = ans[2].toStringWithLine();
		
		Mockito.doReturn(ans).when(mc).readAnswers(category);
		Mockito.doReturn(null).when(tf).readAnswers(category);
		assertTrue(c.onSearchButtonPressed(category));
		//verify
		Mockito.verify(mc).readAnswers(category);
		Mockito.verify(tf).readAnswers(category);
		Mockito.verify(v).displayQuizMessages(captor.capture());
		String finalStr = str[0] + System.lineSeparator() + str[1] + System.lineSeparator() + str[2] + System.lineSeparator();
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
		String[] str = new String[3];
		ans[0] = new AnswerTF(4, category, "question01", true, "caption");
		str[0] = ans[0].toStringWithLine();
		ans[1] = new AnswerTF(7, category, "question02", false, "caption");
		str[1] = ans[1].toStringWithLine();
		ans[2] = new AnswerTF(99, category, "question03", true, "caption");
		str[2] = ans[2].toStringWithLine();
		
		//readAnswers
		Mockito.doReturn(null).when(mc).readAnswers(category);
		Mockito.doReturn(ans).when(tf).readAnswers(category);
		assertTrue(c.onSearchButtonPressed(category));
		//verify
		Mockito.verify(mc).readAnswers(category);
		Mockito.verify(tf).readAnswers(category);
		Mockito.verify(v).displayQuizMessages(captor.capture());
		String finalStr = str[0] + System.lineSeparator() + str[1] + System.lineSeparator() + str[2] + System.lineSeparator();
		assertEquals(finalStr, captor.getValue());
	}
	
	@Test
	public void onSearchReturnMCTF() throws FileNotFoundException, IOException {
		String category = "categ";
		IAnswers[] ansMC = new AnswerMC[3];
		IAnswers[] ansTF = new AnswerTF[3];
		String[] ansStr = new String[6];
		//answerMC
		ansMC[0] = new AnswerMC(1, category, "question01", "A", "B", "C", "D", "A", "caption");
		ansStr[0] = ansMC[0].toStringWithLine();
		ansMC[1] = new AnswerMC(2, category, "question02", "A", "B", "C", "D", "A", "caption");
		ansStr[1] = ansMC[1].toStringWithLine();
		ansMC[2] = new AnswerMC(3, category, "question03", "A", "B", "C", "D", "A", "caption");
		ansStr[2] = ansMC[2].toStringWithLine();
		
		//answerTF
		ansTF[0] = new AnswerTF(3, category, "question01", true, "caption");
		ansStr[3] = ansTF[0].toStringWithLine();
		ansTF[1] = new AnswerTF(5, category, "question02", false, "caption");
		ansStr[4] = ansTF[1].toStringWithLine();
		ansTF[2] = new AnswerTF(8, category, "question03", true, "caption");
		ansStr[5] = ansTF[2].toStringWithLine();
		
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
		//TODO : inserire "File MC" e "FIle TF"
		String finalStr = "";
		for (int i=0; i<6; i++) {
			finalStr += ansStr[i] + System.lineSeparator();
		}
		assertEquals(finalStr, captor.getValue());
	}
	
	/*** Constructor 
	 * @throws Exception ***/
	
	@Test(expected = IllegalArgumentException.class)
	public void ConstructorTest01() throws Exception {
		Controller c = new Controller(null, tf, v);
	}	
	
	@Test(expected = IllegalArgumentException.class)
	public void ConstructorTest02() throws Exception {
		Controller c = new Controller(mc, null, v);
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void ConstructorTest03() throws Exception {
		Controller c = new Controller(mc, tf, null);
	}
	/******************/
}
