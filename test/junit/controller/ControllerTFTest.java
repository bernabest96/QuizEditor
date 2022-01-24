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
import org.mockito.Matchers;
import org.mockito.Mock;
import org.mockito.Mockito;
import org.mockito.Spy;
import org.mockito.internal.verification.Times;
import org.mockito.runners.MockitoJUnit44Runner;

import abbot.finder.Matcher;
import controller.Controller;
import model.AnswerMC;
import model.AnswerTF;
import model.McModel;
import model.TfModel;
import view.View;

@RunWith(MockitoJUnit44Runner.class)
public class ControllerTFTest {

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
	
	/** onChangeTFFilePath Testing*/
	
	@Test(expected = IllegalArgumentException.class)
	public void ChangePathTFNotNull() {
		c.onChangeTFFilePath(null);
	}
	
	@Test
	public void ChangePathTFFileNotFound() throws FileNotFoundException {
		String not_exists_file = "file_non_esite.txt";
		Mockito.doThrow(new FileNotFoundException()).when(tf).setFile(not_exists_file);
		assertFalse(c.onChangeTFFilePath(not_exists_file));
		Mockito.verify(tf).setFile(not_exists_file);
		Mockito.verify(v).displayInfoErrorMessages(Controller.getFileNotFoundMessage() + not_exists_file);
	}
	
	@Test
	public void ChangePathTFNotCorrect() throws FileNotFoundException, IOException {
		String file_not_ok = "quiz_tf_not_ok.txt";
		Mockito.doNothing().when(tf).setFile(Mockito.anyString());
		Mockito.when(tf.hasKeyWords()).thenReturn(false);
//		Mockito.when(mc.hasWrongLines()).thenReturn(false);
		assertFalse(c.onChangeTFFilePath(file_not_ok));
		//verify
		Mockito.verify(tf).setFile(file_not_ok);
		Mockito.verify(tf, Mockito.atLeastOnce()).hasKeyWords();
		Mockito.verify(v).displayInfoErrorMessages(Mockito.anyString());
//		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
//		assertTrue(captor.getValue().contains(file_not_ok));
	}
	
	//controlla se funzia onChangeTFFilePath
	@Test
	public void ChangePathTFCorrect() throws IOException {
		String file_exists_tf = "quiz_tf.txt";
		Mockito.when(tf.hasKeyWords()).thenReturn(true);
		Mockito.when(tf.hasWrongLines()).thenReturn(false);
		assertTrue(c.onChangeTFFilePath(file_exists_tf));
		//verify
		Mockito.verify(tf).setFile(file_exists_tf);
		Mockito.verify(tf, Mockito.times(2)).hasKeyWords();
		Mockito.verify(tf).hasWrongLines();
		Mockito.verify(v).displayInfoErrorMessages(Controller.getChangedFileMessage() + file_exists_tf);
	}
	
	@Test
	public void ChangePathIOExceptionTest() throws IOException {
		String file_exists_tf = "quiz_tf.txt";
		Mockito.doThrow(new IOException()).when(tf).hasKeyWords();
		Mockito.doNothing().when(tf).setFile(file_exists_tf);
		assertFalse(c.onChangeTFFilePath(file_exists_tf));
		//verify
		Mockito.verify(tf).setFile(file_exists_tf);
		Mockito.verify(tf, Mockito.atLeastOnce()).hasKeyWords();
		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
		assertEquals(Controller.getGeneralErrorMessage(), captor.getValue());
	}
	
	/******************/
	
	/** InsertTF TESTS*/
	
	@Test(expected = IllegalArgumentException.class)
	public void InsertTFNullTest() {
		c.onInsertTFButtonPressed("", null, true, "");
	}
	
	@Test
	public void InsertTFEmpty01Test() {
		assertFalse(c.onInsertTFButtonPressed("", "question", true, "caption"));
		Mockito.verify(v).displayInfoErrorMessages(Controller.getParameterEmpty01());
	}
	
	@Test
	public void InsertTFhasKeysTest() throws FileNotFoundException, IOException {
		//first and seocnd line
		String first_line = "\"TF\"";
		Mockito.when(tf.getFirstLine()).thenReturn(first_line);
		String second_line = "\"category\",\"question\",\"answer\",\"caption\"";
		Mockito.when(tf.getSecondLine()).thenReturn(second_line);
		//haskey
		Mockito.when(tf.hasKeyWords()).thenReturn(false);
		assertFalse(c.onInsertTFButtonPressed("category", "question", true, "caption"));
		Mockito.verify(tf).hasKeyWords();
		Mockito.verify(v).displayInfoErrorMessages(Controller.getNotCorrectFileMessage() + 
				System.lineSeparator() + tf.getFirstLine() +
				System.lineSeparator() + tf.getSecondLine());
	}
	
	@Test
	public void InsertTFhasWrongLineTest() throws FileNotFoundException, IOException {
		String first_line = "\"TF\"";
		Mockito.when(tf.getFirstLine()).thenReturn(first_line);
		String second_line = "\"category\",\"question\",\"answer\",\"caption\"";
		Mockito.when(tf.getSecondLine()).thenReturn(second_line);
		//haskeywords and wrong lines
		Mockito.when(tf.hasKeyWords()).thenReturn(true);
		Mockito.when(tf.hasWrongLines()).thenReturn(true);
		Mockito.when(tf.removeWrongLines()).thenReturn(true);
		Mockito.when(tf.insertAnswer(Matchers.any(AnswerTF.class))).thenReturn(true);
		assertTrue(c.onInsertTFButtonPressed("category", "question", true, "caption"));
		Mockito.verify(tf, Mockito.times(2)).hasKeyWords();
		Mockito.verify(tf).hasWrongLines();
		Mockito.verify(v,Mockito.atLeast(2)).displayInfoErrorMessages(captor.capture());
		//prendi la seconda chiamata
		assertEquals(Controller.getWrongLinesMessage(), captor.getAllValues().get(0));
		assertEquals(Controller.getRemovedLinesMessage(), captor.getAllValues().get(1));
	}
	
	
	@Test
	public void InsertMCremoveLineTest() throws FileNotFoundException, IOException {
		Mockito.when(tf.hasKeyWords()).thenReturn(true);
		Mockito.when(tf.hasWrongLines()).thenReturn(true);
		Mockito.when(tf.removeWrongLines()).thenReturn(false);
		assertFalse(c.onInsertTFButtonPressed("category", "question", true, "caption"));
		Mockito.verify(tf, Mockito.times(2)).hasKeyWords();
		Mockito.verify(tf).hasWrongLines();
		Mockito.verify(v,Mockito.atLeast(2)).displayInfoErrorMessages(captor.capture());
		//prendi la seconda chiamata
		assertEquals(Controller.getWrongLinesMessage(), captor.getAllValues().get(0));
		assertEquals(Controller.getCannotRemoveLines(), captor.getAllValues().get(1));
	}
	
	
	
	
	
	@SuppressWarnings("deprecation")
	@Test
	public void InsertTFFileNotFoundTest() throws IOException {
		Mockito.doThrow(new FileNotFoundException()).when(tf).hasKeyWords();
		Mockito.doThrow(new FileNotFoundException()).when(tf).hasWrongLines();
		Mockito.doThrow(new FileNotFoundException()).when(tf).insertAnswer(Mockito.any(AnswerTF.class));
		assertFalse(c.onInsertTFButtonPressed("category", "question", true, "caption"));
		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
		assertThat(captor.getValue(), CoreMatchers.containsString(Controller.getFileNotFoundMessage()));
	}
	
	@Test
	public void InsertTFOKTest() throws IOException {
		//Mocks
//		non puoi fare lo stub dei metodi equals() e hashCode();
//		Mockito.when(a.equals(Mockito.anyObject())).thenReturn(false);
		Mockito.when(tf.hasKeyWords()).thenReturn(true);
		Mockito.when(tf.hasWrongLines()).thenReturn(false);
		Mockito.when(tf.insertAnswer(Mockito.any(AnswerTF.class))).thenReturn(true);
		assertTrue(c.onInsertTFButtonPressed("categ02", "question02", true, "caption02"));
		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
		assertEquals(Controller.getInsertedQuiz(), captor.getValue());
	}
	
	@Test
	public void InsertDuplicateTest() throws FileNotFoundException, IOException {
		Mockito.when(tf.hasKeyWords()).thenReturn(true);
		Mockito.when(tf.hasWrongLines()).thenReturn(false);
		Mockito.when(tf.insertAnswer(Mockito.any(AnswerTF.class))).thenReturn(true);
		//this should be ok
		assertTrue(c.onInsertTFButtonPressed("categ", "question", true, "caption"));
		//this is an error due to duplicate insert
		assertFalse(c.onInsertTFButtonPressed("categ", "question", true, "caption"));
		Mockito.verify(v, Mockito.times(2)).displayInfoErrorMessages(captor.capture());
		assertEquals(Controller.getJustInsertedMessage(), captor.getValue() /*captor.getAllValues().get(1)*/);
	}
	
	@Test
	public void InsertGeneralIOException() throws FileNotFoundException, IOException {
		Mockito.doThrow(new IOException()).when(tf).hasKeyWords();
		assertFalse(c.onInsertTFButtonPressed("categ", "question", true, "caption"));
		Mockito.verify(v).displayInfoErrorMessages(captor.capture());
		assertEquals(Controller.getGeneralErrorMessage(), captor.getValue());
	}
	
	
	@Test
	public void InsertInjectionTest01() throws FileNotFoundException, IOException {
		Mockito.when(tf.hasKeyWords()).thenReturn(true);
		Mockito.when(tf.hasWrongLines()).thenReturn(false);
		Mockito.when(tf.insertAnswer(Mockito.any(AnswerTF.class))).thenReturn(true);
		//injection
		assertTrue(c.onInsertTFButtonPressed("category", "this is a \",\" question", true, "caption"));
		Mockito.verify(v, Mockito.atLeastOnce()).displayInfoErrorMessages(captor.capture());
		assertEquals(Controller.getMoreInjectionString(), captor.getAllValues().get(0));
		assertEquals(Controller.getInsertedQuiz(), captor.getAllValues().get(1));
		
	}
	
	/******************************/
}
