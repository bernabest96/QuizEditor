package junit.controller;

import static org.junit.Assert.*;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.regex.Matcher;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.mockito.ArgumentCaptor;
import org.mockito.Captor;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.Mockito;
import org.mockito.junit.MockitoJUnit;
import org.mockito.junit.MockitoRule;
import org.mockito.runners.MockitoJUnit44Runner;

import controller.Controller;
import model.AnswerMC;
import model.McModel;
import model.TfModel;
import view.View;

@RunWith(Parameterized.class)
public class ControllerInsertMCTestMCDC {

	@Rule 
	public MockitoRule rule = MockitoJUnit.rule();
	
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
	
	//fields
	String category;
	String question;
	String[] answers;
	String ans;
	String caption;
	boolean throwsException;
	private String message;
	boolean injectionCheck;
	
	@Parameters
	public static Collection<Object[]> data() {
        Object[][] data = new Object[][] {
        	//check all null references
        	{null, "question", new String[] {"A", "B", "C", "D"}, "A", "caption", true, null, false},
        	{"categ",null, new String[] {"A", "B", "C", "D"}, "A", "caption", true, null, false},
        	{"categ","question", null, "A", "caption", true, null, false},
        	{"categ","question", new String[] {"A", "B", "C", "D"}, null, "caption", true, null, false},
        	{"categ","question", new String[] {"A", "B", "C", "D"}, "A", null, true, null, false},
        	{"categ","question", new String[] {null, "B", "C", "D"}, "A", "caption", true, null, false},
        	{"categ","question", new String[] {"A", null, "C", "D"}, "A", "caption", true, null, false},
        	{"categ","question", new String[] {"A", "B", null, "D"}, "A", "caption", true, null, false},
        	{"categ","question", new String[] {"A", "B", "C", null}, "A", "caption", true, null, false},
        	//A, B, C, D and error
        	{"categ","question", new String[] {"A", "B", "C", "D"}, "A", "caption", false, null, false},
        	{"categ","question", new String[] {"A", "B", "C", "D"}, "B", "caption", false, null, false},
        	{"categ","question", new String[] {"A", "B", "C", "D"}, "C", "caption", false, null, false},
        	{"categ","question", new String[] {"A", "B", "C", "D"}, "D", "caption", false, null, false},
        	{"categ","question", new String[] {"A", "B", "C", "D"}, "Risposta", "caption", true, null, false},
        	//empty strings
        	{"","question", new String[] {"A", "B", "C", "D"}, "A", "caption", false, Controller.getParameterEmpty01(), false},
        	{"categ","", new String[] {"A", "B", "C", "D"}, "A", "caption", false, Controller.getParameterEmpty01(), false},
        	{"categ","question", new String[] {"", "B", "C", "D"}, "A", "caption", false, Controller.getParameterEmpty02(), false},
        	{"categ","question", new String[] {"A", "", "C", "D"}, "A", "caption", false, Controller.getParameterEmpty02(), false},
        	{"categ","question", new String[] {"A", "B", "", "D"}, "A", "caption", false, Controller.getParameterEmpty02(), false},
        	{"categ","question", new String[] {"A", "B", "C", ""}, "A", "caption", false, Controller.getParameterEmpty02(), false},
        	{"categ","question", new String[] {"A", "B", "C", "D"}, "", "caption", true, null, false},
        	{"categ","question", new String[] {"A", "B", "C", "D"}, "A", "", false, Controller.getParameterEmpty01(), false},
        	//insert injections
        	{"categ with \",\" injection","question", new String[] {"A", "B", "C", "D"}, "A", "caption", false, null, true},
        	{"categ","question with \",\" injection", new String[] {"A", "B", "C", "D"}, "A", "caption", false,  null, true},
        	{"categ","question", new String[] {"A with \",\" injection", "B", "C", "D"}, "A", "caption", false,  null, true},
        	{"categ","question", new String[] {"A", "B with \",\" injection", "C", "D"}, "A", "caption", false,  null, true},
        	{"categ","question", new String[] {"A", "B", "C with \",\" injection", "D"}, "A", "caption", false,  null, true},
        	{"categ","question", new String[] {"A", "B", "C", "D with \",\" injection"}, "A", "caption", false,  null, true},
        	{"categ","question", new String[] {"A", "B", "C", "D"}, "A", "caption with \",\" injection", false,  null, true},
        };
        return Arrays.asList(data);
    }
	
	public ControllerInsertMCTestMCDC(String category, String question, String[] answers, String ans, 
			String caption, boolean throwsException, String message, boolean injectionCheck) {
		this.category = category;
		this.question = question;
		this.answers = answers;
		this.ans = ans;
		this.caption = caption;
		this.throwsException = throwsException;
		this.message = message;
		this.injectionCheck = injectionCheck;
	}
	
	@Before
	public void setUp() throws Exception {
		c = new Controller(mc, tf, v);
	}
	
	@Test
	public void ControllerThrowsIllegalArgException() {
		if (throwsException) {
			assertThrows(IllegalArgumentException.class, () -> {
				c.onInsertMCButtonPressed(category, question, answers, ans, caption);
			});
		}else {
			c.onInsertMCButtonPressed(category, question, answers, ans, caption);
		}
	}
	
	@Test
	public void EmptyStringTest() {
		if (message != null) {
			assertFalse(c.onInsertMCButtonPressed(category, question, answers, ans, caption));
			Mockito.verify(v).displayInfoErrorMessages(message);
		}
	}
	
	@Test
	public void InjectionTest() throws IOException {
		if (injectionCheck) {
			Mockito.doReturn(true).when(mc).hasKeyWords();
			Mockito.doReturn(false).when(mc).hasWrongLines();			
			Mockito.doReturn(true).when(mc).insertAnswer(Mockito.any(AnswerMC.class));
			assertTrue(c.onInsertMCButtonPressed(category, question, answers, ans, caption));
			Mockito.verify(v, Mockito.atLeastOnce()).displayInfoErrorMessages(captor.capture());
//			System.out.println(captor.getAllValues().toString());
			assertTrue(captor.getAllValues().contains(Controller.getMoreInjectionString()));
		}
	}

}
