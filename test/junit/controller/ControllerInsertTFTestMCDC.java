package junit.controller;

import static org.junit.Assert.*;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

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

import controller.Controller;
import model.AnswerMC;
import model.McModel;
import model.TfModel;
import view.View;

@RunWith(Parameterized.class)
public class ControllerInsertTFTestMCDC {

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
	boolean ans;
	String caption;
	boolean throwsException;
	private String message;
	boolean injectionCheck;
	
	@Parameters
	public static Collection<Object[]> data() {
        Object[][] data = new Object[][] {
        	//check all null references
        	{null,"question", true, "caption", true, null, false},
        	{"categ",null, true, "caption", true, null, false},
        	{"categ","question", true, null, true, null, false},
        	{"categ","question", true, "caption", false, null, false},
        	//empty strings
        	{"","question", true, "caption", false, Controller.getParameterEmpty01(), false},
        	{"categ","", true, "caption", false, Controller.getParameterEmpty01(), false},
        	{"categ","question", true, "", false, Controller.getParameterEmpty01(), false},
        	//insert injections
        	{"categ with \",\" injection","question", true, "caption", false, null, true},
        	{"categ","question with \",\" injection", false, "caption", false,  null, true},
        	{"categ","question", false, "caption with \",\" injection", false,  null, true},
       
        };
        return Arrays.asList(data);
    }
	
	public ControllerInsertTFTestMCDC(String category, String question, boolean ans, 
			String caption, boolean throwsException, String message, boolean injectCheck) {
		this.category = category;
		this.question = question;
		this.ans = ans;
		this.caption = caption;
		this.throwsException = throwsException;
		this.message = message;
		this.injectionCheck = injectCheck;
	}
	
	@Before
	public void setUp() throws Exception {
		c = new Controller(mc, tf, v);
	}
	
	@Test
	public void ControllerThrowsIllegalArgException() {
		if (throwsException) {
			assertThrows(IllegalArgumentException.class, () -> {
				c.onInsertTFButtonPressed(category, question, ans, caption);
			});
		}else {
			c.onInsertTFButtonPressed(category, question, ans, caption);
		}
	}
	
	@Test
	public void EmptyStringTest() {
		if (message != null) {
			assertFalse(c.onInsertTFButtonPressed(category, question, ans, caption));
			Mockito.verify(v).displayInfoErrorMessages(message);
		}
	}
	
	@Test
	public void InjectionTest() throws IOException {
		if (injectionCheck) {
			Mockito.doReturn(true).when(tf).hasKeyWords();
			Mockito.doReturn(false).when(tf).hasWrongLines();			
			Mockito.doReturn(true).when(tf).insertAnswer(Mockito.any(AnswerMC.class));
			assertTrue(c.onInsertTFButtonPressed(category, question, ans, caption));
			Mockito.verify(v, Mockito.atLeastOnce()).displayInfoErrorMessages(captor.capture());
//			System.out.println(captor.getAllValues().toString());
			assertTrue(captor.getAllValues().contains(Controller.getMoreInjectionString()));
		}
	}

}
