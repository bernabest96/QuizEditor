package junit.controller;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

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
public class ControllerMCTest {
	
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
		Mockito.verify(v).displayInfoErrorMessages(c.getFileNotFoundMessage() + not_exists_file);
	}

	@Test
	public void ChangePathMCFileNotFound() throws FileNotFoundException {
		String not_exists_file = "file_non_esite.txt";
		Mockito.doThrow(new FileNotFoundException()).when(mc).setFile(not_exists_file);
		assertFalse(c.onChangeMCFilePath(not_exists_file));
		Mockito.verify(mc).setFile(not_exists_file);
		Mockito.verify(v).displayInfoErrorMessages(Controller.getFileNotFoundMessage() + not_exists_file);
	}
	
	@Test
	public void ChangePathMCCorrect() throws IOException {
		String file_exists_tf = "quiz_tf.txt";
		Mockito.when(mc.hasKeyWords()).thenReturn(true);
		Mockito.when(mc.hasWrongLines()).thenReturn(false);
		assertTrue(c.onChangeMCFilePath(file_exists_tf));
		//verify
		Mockito.verify(mc).setFile(file_exists_tf);
		Mockito.verify(mc, Mockito.times(2)).hasKeyWords();
		Mockito.verify(mc).hasWrongLines();
		Mockito.verify(v).displayInfoErrorMessages(Controller.getChangedFileMessage() + file_exists_tf);
	}
	
	/** onInsertMCButtonPressed Testing**/
	@Test(expected = IllegalArgumentException.class)
	public void InsertMCNull01Test() {
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
		//first and seocnd line
		String first_line = "\"MC\"";
		Mockito.when(mc.getFirstLine()).thenReturn(first_line);
		String second_line = "\"category\",\"question\",\"A\",\"B\",\"C\",\"D\",\"answer\",\"caption\"";
		Mockito.when(mc.getSecondLine()).thenReturn(second_line);
		//haskey
		Mockito.when(mc.hasKeyWords()).thenReturn(false);
		assertFalse(c.onInsertMCButtonPressed("category", "question", new String[] {"A", "B", "C", "D"}, "A", "caption"));
		Mockito.verify(mc).hasKeyWords();
		Mockito.verify(v).displayInfoErrorMessages(Controller.getNotCorrectFileMessage() + 
				System.lineSeparator() + mc.getFirstLine() +
				System.lineSeparator() + mc.getSecondLine());
	}
	
	@Test
	public void InsertMChasWrongLineTest() throws FileNotFoundException, IOException {
		String first_line = "\"MC\"";
		Mockito.when(mc.getFirstLine()).thenReturn(first_line);
		String second_line = "\"category\",\"question\",\"A\",\"B\",\"C\",\"D\",\"answer\",\"caption\"";
		Mockito.when(mc.getSecondLine()).thenReturn(second_line);
		//haskeywords and wrong lines
		Mockito.when(mc.hasKeyWords()).thenReturn(true);
		Mockito.when(mc.hasWrongLines()).thenReturn(true);
		assertFalse(c.onInsertMCButtonPressed("category", "question", new String[] {"A", "B", "C", "D"}, "A", "caption"));
		Mockito.verify(mc, Mockito.times(2)).hasKeyWords();
		Mockito.verify(mc).hasWrongLines();
		Mockito.verify(v).displayInfoErrorMessages(Controller.getWrongLinesMessage());
	}
	
	@SuppressWarnings("deprecation")
	@Test
	public void InsertTFFileNotFoundTest() throws IOException {
		Mockito.doThrow(new FileNotFoundException()).when(mc).hasKeyWords();
		Mockito.doThrow(new FileNotFoundException()).when(mc).hasWrongLines();
		Mockito.doThrow(new FileNotFoundException()).when(mc).insertAnswer(Mockito.any(AnswerTF.class));
		assertFalse(c.onInsertMCButtonPressed("category", "question", new String[] {"A", "B", "C", "D"}, "A", "caption"));
		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
		assertThat(captor.getValue(), CoreMatchers.containsString(Controller.getFileNotFoundMessage()));
	}
	
	@Test
	public void InsertTFOKTest() throws IOException {
		//Mocks
//		non puoi fare lo stub dei metodi equals() e hashCode();
//		Mockito.when(a.equals(Mockito.anyObject())).thenReturn(false);
		Mockito.when(mc.hasKeyWords()).thenReturn(true);
		Mockito.when(mc.hasWrongLines()).thenReturn(false);
		Mockito.when(mc.insertAnswer(Mockito.any(AnswerTF.class))).thenReturn(true);
		assertTrue(c.onInsertMCButtonPressed("category", "question", new String[] {"A", "B", "C", "D"}, "A", "caption"));
		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
		assertEquals(Controller.getInsertedQuiz(), captor.getValue());
	}
	
	/******************************************************************/
	/***********JUnit Testing for Statement Coverage*******************/
	
	
	
	
	
	
	
	
	
	/*****************************/
}
