package junit.controller;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.Mockito;
import org.mockito.runners.MockitoJUnit44Runner;
import org.mockito.runners.MockitoJUnitRunner;

import controller.Controller;
import junit.framework.Assert;
import model.AnswerMC;
import model.AnswerTF;
import model.IAnswers;
import model.McModel;
import model.Model;
import model.TfModel;
import view.View;

@RunWith(MockitoJUnit44Runner.class)
public class ControllerTest {
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
	
	/** onChangeMCFilePath Testing*/
	
	//input : null pointer
	@Test(expected = IllegalArgumentException.class)
	public void ChangePathMCNullInput() {
		c.onChangeMCFilePath(null);
	}
	
	
	@Test
	public void ChangePathMCNotExistFile() throws FileNotFoundException {
		String not_exists_file = "file_non_esite.txt";
		Mockito.doThrow(new FileNotFoundException()).when(mc).setFile(not_exists_file);
		assertFalse(c.onChangeMCFilePath(not_exists_file));
		Mockito.verify(mc).setFile(not_exists_file);
	}

	@Test
	public void ChangePathMCisWellFormed() throws IOException {
		String file_exist_mc = "quiz_mc.txt";
		Mockito.doNothing().when(mc).setFile(file_exist_mc);
		Mockito.when(mc.isWellFormed()).thenReturn(true);
		assertTrue(c.onChangeMCFilePath(file_exist_mc));
		Mockito.verify(mc).setFile(file_exist_mc);
		Mockito.verify(mc).isWellFormed();
	}
	
	@Test
	public void ChangePathMCNotWellFormed() throws IOException {
		String file_wrong_mc = "exist_but_not_wellformed.txt";
		Mockito.doNothing().when(mc).setFile(file_wrong_mc);
		Mockito.when(mc.isWellFormed()).thenReturn(false);
		assertFalse(c.onChangeMCFilePath(file_wrong_mc));
		Mockito.verify(mc).setFile(file_wrong_mc);
		Mockito.verify(mc).isWellFormed();
	}
	
	/** onChangeTFFilePath Testing*/
	
	@Test(expected = IllegalArgumentException.class)
	public void ChangePath02() {
		c.onChangeTFFilePath(null);
	}
	
	@Test
	public void ChangePath04() throws FileNotFoundException {
		String not_exists_file = "file_non_esite.txt";
		Mockito.doThrow(new FileNotFoundException()).when(tf).setFile(not_exists_file);
		assertFalse(c.onChangeTFFilePath(not_exists_file));
		Mockito.verify(tf).setFile(not_exists_file);
	}
	
	
	//controlla se funzia onChangeTFFilePath
	@Test
	public void ChangePath06() throws IOException {
		String file_exists_tf = "quiz_tf.txt";
		Mockito.doNothing().when(tf).setFile(file_exists_tf);
		Mockito.when(tf.isWellFormed()).thenReturn(true);
		assertTrue(c.onChangeTFFilePath(file_exists_tf));
		Mockito.verify(tf).setFile(file_exists_tf);
		Mockito.verify(tf).isWellFormed();
	}
	
	
	/*
	//throw general error
	@Test
	public void ChangePath08() throws FileNotFoundException {
		String some_file = "some_file.txt";
		Mockito.doThrow(new IOException()).when(mc).setFile(some_file);
		assertFalse(c.onChangeMCFilePath(some_file));
		Mockito.verify(mc).setFile(some_file);
	}
	*/
	
	/** onInsertMCButtonPressed Testing**/
	@Test(expected = IllegalArgumentException.class)
	public void InsertMCNullTest() {
		c.onInsertMCButtonPressed("", "", null, "stringa", "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void InsertMCNull02Test() {
		c.onInsertMCButtonPressed("caption", "", new String[] {"", "dsad"}, "A", "caption");
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void InsertMCNull03Test() {
		c.onInsertMCButtonPressed("caption", "asd", new String[] {"dasd", "dsad", "das", "das"}, "risposta", "caption");
	}
	
	@Test
	public void InsertMCEmpty01Test() {
		String[] answers = new String[] {"A", "B", "C", "D"};
		assertFalse(c.onInsertMCButtonPressed("", "question", answers, "B", "caption"));
		Mockito.verify(v).displayInfoErrorMessages(Controller.getParameterEmpty01());
	}
	
	@Test
	public void InsertMCEmpty02Test() {
		String[] answers = new String[] {"A", "", "C", "D"};
		assertFalse(c.onInsertMCButtonPressed("category", "question", answers, "C", "caption"));
		Mockito.verify(v).displayInfoErrorMessages(Controller.getParameterEmpty02());
	}
	
	@Test
	public void InsertMChasKeysTest() throws FileNotFoundException, IOException {
		String[] answers = new String[] {"A", "B", "C", "D"};
		Mockito.when(mc.hasKeyWords()).thenReturn(false);
		assertFalse(c.onInsertMCButtonPressed("cat", "ques", answers, "B", "cap"));
		Mockito.verify(mc).hasKeyWords();
		Mockito.verify(v).displayInfoErrorMessages(Controller.getNotCorrectFileMessage());
	}
	
	
	
	@Test
	public void InsertMCIOExcepTest() throws IOException {
		String[] answers = new String[] {"A", "B", "C", "D"};
		AnswerMC a =  Mockito.mock(AnswerMC.class);
		Mockito.doThrow(new IOException()).when(mc).insertAnswer(a);
		assertFalse(c.onInsertMCButtonPressed("cat", "ques", answers, "B", "cap"));
		Mockito.verify(v).displayInfoErrorMessages(Controller.getGeneralErrorMessage());
	}
	
	/**onSearchButtonPressed Testing**/
	
	@Test(expected = IllegalArgumentException.class)
	public void onSearchNullTest() {
		c.onSearchButtonPressed(null);
	}
	
	@Test
	public void onSearchFileNotFoundTest01() throws FileNotFoundException, IOException {
		String filename = "file.txt";
		Mockito.doNothing().when(mc).setFile(filename);
		Mockito.doThrow(new FileNotFoundException()).when(mc).readAnswers("");
		assertFalse(c.onSearchButtonPressed(""));
		Mockito.verify(mc).readAnswers("");
		Mockito.verify(v).displayInfoErrorMessages(Controller.getFileNotFoundMessage() + filename);
	}
	
	@Test
	public void onSearchIOExceptionTest() throws FileNotFoundException, IOException {
		Mockito.doThrow(new IOException()).when(tf).readAnswers("");
		assertFalse(c.onSearchButtonPressed(""));
		Mockito.verify(mc).readAnswers("");
		Mockito.verify(tf).readAnswers("");
		Mockito.verify(v).displayInfoErrorMessages(Controller.getGeneralErrorMessage());
	}
	
	//testa quando non ci sono risposte
	@Test
	public void onSearchNothingReturn() throws FileNotFoundException, IOException {
		String category = "cat_a";
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
		Mockito.doReturn(true).when(mc).isWellFormed();
		Mockito.doReturn(true).when(tf).isWellFormed();
		Mockito.doReturn(true).when(mc).hasKeyWords();
		Mockito.doReturn(false).when(mc).hasWrongLines();
		
		IAnswers[] ans = new AnswerMC[3];
		for (int i=0; i < ans.length; i++) {
			ans[i] = new AnswerMC(category, "question", "A", "B", "C", "D", "A", "caption");
		}
		Mockito.doReturn(ans).when(mc).readAnswers(category);
		Mockito.doReturn(null).when(tf).readAnswers(category);
		assertTrue(c.onSearchButtonPressed(category));
		//verify
		Mockito.verify(mc).readAnswers(category);
		Mockito.verify(tf).readAnswers(category);
		String quiz = "";
		for (IAnswers a : ans) {
			AnswerMC aMC = (AnswerMC) a;
			quiz += aMC.toString() + System.lineSeparator();
		}
		Mockito.verify(v).displayQuizMessages(quiz);
	}
	
	@Test
	public void onSearchReturnOnlyTF() throws FileNotFoundException, IOException {
		String category = "tf_cat";
		IAnswers[] ans = new AnswerTF[3];
		String quiz = "";
		for (int i=0; i < ans.length; i++) {
			ans[i] = new AnswerTF(category, "question", true, "caption");
			quiz += ans[i].toString() + System.lineSeparator();
		}
		Mockito.doReturn(null).when(mc).readAnswers(category);
		Mockito.doReturn(ans).when(tf).readAnswers(category);
		assertTrue(c.onSearchButtonPressed(category));
		//verify
		Mockito.verify(mc).readAnswers(category);
		Mockito.verify(tf).readAnswers(category);
		Mockito.verify(v).displayQuizMessages(quiz);
	}
	
	@Test
	public void onSearchReturnMCTF() throws FileNotFoundException, IOException {
		String category = "mc_cat";
		IAnswers[] ansMC = new AnswerMC[3];
		IAnswers[] ansTF = new AnswerTF[3];
		String quiz = "";
		assertTrue(ansMC.length == ansTF.length);
		for (int i=0; i < ansMC.length; i++) {
			ansMC[i] = new AnswerMC(category, "question", "A", "B", "C", "D", "A", "caption");
			ansTF[i] = new AnswerTF(category, "question", true, "caption");
			quiz += ansMC[i].toString() + System.lineSeparator();
			quiz += ansTF[i].toString() + System.lineSeparator();
		}
		Mockito.doReturn(ansMC).when(mc).readAnswers(category);
		Mockito.doReturn(ansTF).when(tf).readAnswers(category);
		assertTrue(c.onSearchButtonPressed(category));
		//verify
		Mockito.verify(mc).readAnswers(category);
		Mockito.verify(tf).readAnswers(category);
		Mockito.verify(v).displayQuizMessages(quiz);
	}
	
	
}
