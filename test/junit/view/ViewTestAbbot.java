package junit.view;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.awt.Component;
import java.awt.Point;
import java.awt.event.ActionEvent;

import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JMenuItem;
import javax.swing.JTextField;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.InjectMocks;
import org.mockito.Matchers;
import org.mockito.Mock;
import org.mockito.Mockito;
import org.mockito.runners.MockitoJUnit44Runner;

import abbot.finder.ComponentNotFoundException;
import abbot.finder.Matcher;
import abbot.finder.MultipleComponentsFoundException;
import abbot.tester.ComponentLocation;
import abbot.tester.JButtonTester;
import abbot.tester.JFileChooserTester;
import controller.Controller;
import controller.IController;
import junit.extensions.abbot.ComponentTestFixture;
import view.View;

@RunWith(MockitoJUnit44Runner.class)
public class ViewTestAbbot extends ComponentTestFixture{
	@Mock
	IController c;
	
	@InjectMocks
	View v;
	
	@Before
	public void setup() {
		v = new View();
		assertNotNull(c);
		v.registerListener(c);
	}
		
	@Test
	public void insertMC() throws ComponentNotFoundException, MultipleComponentsFoundException {
		
		JButtonTester tester = new JButtonTester();
		
		String category = "categoria_a";
		v.getCategoryMCField().setText(category);
		String question = "La domanda?";
		v.getQuestionMCField().setText(question);
		String risp_a = "risposta A";
		v.getAField().setText(risp_a);
		String risp_b = "risposta B";
		v.getBField().setText(risp_b);
		String risp_c = "risposta C";
		v.getCField().setText(risp_c);
		String risp_d = "risposta D";
		v.getDField().setText(risp_d);
		v.getARadioButton().setSelected(false);
		v.getBRadioButton().setSelected(false);
		v.getCRadioButton().setSelected(true);
		v.getDRadioButton().setSelected(false);
		String caption = "this is caption";
		v.getCaptionMCField().setText(caption);
        
        JButton button = (JButton) getFinder().find(v, new Matcher() {
			
			@Override
			public boolean matches(Component c) {
				// TODO Auto-generated method stub
				return c instanceof JButton && ((JButton) c).getText().equals("Insert!");
			}
		});
        
		tester.actionDelay(1000);
        tester.actionMouseMove(button, new ComponentLocation(new Point(0, 0)));
        tester.actionClick(button);
        tester.actionDelay(1000);
		
		String[] ans = new String[] {risp_a, risp_b, risp_c, risp_d};
		Mockito.verify(c).onInsertMCButtonPressed(category, question, ans, "C", caption);
		v.displayInfoErrorMessages(Controller.getInsertedQuiz());
		
	}
	
//	@Test
//	public void insertTF() {
//		ActionEvent e = new ActionEvent(v.getInsertTFButton(), ActionEvent.ACTION_PERFORMED, "");
//		String category = "categoria_tf";
//		v.getCategoryTFField().setText(category);
//		String question = "La domanda su cosa?";
//		v.getQuestionTFField().setText(question);
//		v.getTrueRB().setSelected(false);
//		v.getFalseRB().setSelected(true);
//		String caption = "this is caption";
//		v.getCaptionTFField().setText(caption);
//		v.actionPerformed(e);
//		Mockito.verify(c).onInsertTFButtonPressed(category, question, false, caption);
//	}
//	
//	@Test
//	public void search01() {
//		ActionEvent e = new ActionEvent(v.getSearchButton(), ActionEvent.ACTION_PERFORMED, "");
//		String category = "categoria_tf";
//		v.getCategoryText().setText(category);
//		v.actionPerformed(e);
//		Mockito.verify(c).onSearchButtonPressed(category);
//	}
//	
/*	
	public static String unEscapeString(String s){
	    StringBuilder sb = new StringBuilder();
	    for (int i=0; i<s.length(); i++)
	        switch (s.charAt(i)){
	            case '\n': sb.append("\\n"); break;
	            case '\t': sb.append("\\t"); break;
	            // ... rest of escape characters
	            default: sb.append(s.charAt(i));
	        }
	    return sb.toString();
	}
*/
	
//	@Test
//	public void display01() {
//		String mex01 = "messaggio01";
//		v.displayInfoErrorMessages(mex01);
////		System.out.println(unEscapeString(v.getDisplayError().getText()));
//		assertEquals(mex01 + System.lineSeparator(), v.getDisplayError().getText());
//		String mex02 = "messaggio02";
//		v.displayInfoErrorMessages(mex02);
//		String mex = mex01 + System.lineSeparator() + mex02 + System.lineSeparator();
////		System.out.println(mex);
//		assertEquals( mex, v.getDisplayError().getText());
//	}
//	
//	@Test
//	public void insertMCPanel() {
//		assertTrue(v.getMcPanel().isShowing());
//	}
//	
//	@Test
//	public void insertTfPanel() {
//		ActionEvent e = new ActionEvent(v.getTfRB(), ActionEvent.ACTION_PERFORMED, "");
////		v.getTfRB().setSelected(true);
//		v.actionPerformed(e);
//		assertTrue(!v.getMcRB().isSelected());
//		assertTrue(v.getTfRB().isSelected());
//		assertTrue(!v.getMcPanel().isShowing());
//		assertTrue(v.getTfPanel().isShowing());
//	}
//	
//	@Test
//	public void searchPanel() {
//		ActionEvent e = new ActionEvent(v.getSearchRB(), ActionEvent.ACTION_PERFORMED, "");
////		v.getSearchRB().setSelected(true);
//		v.actionPerformed(e);
//		assertTrue(!v.getInsertRB().isSelected());
//		assertTrue(v.getSearchRB().isSelected());
//		assertTrue(v.getSearchPanel().isShowing());
//		assertTrue(!v.getInsertPanel().isShowing());
//	}
//	
//	
//	
//	  @Test public void setFileMC() throws ComponentNotFoundException, MultipleComponentsFoundException { 
//		  ActionEvent e = new ActionEvent(v.getSearchMc(), ActionEvent.ACTION_PERFORMED, ""); 
//		  JFileChooser fc = v.getFcMc(); 
//		  String filepath = "C:\\file\\qualsiasi";
//		  
////		  JMenuItem mcItem = (JMenuItem) getFinder().find(new Matcher() {
////			
////			@Override
////			public boolean matches(Component c) {
////				return c instanceof JMenuItem && ((JMenuItem) c).getText().equals("Choose File for Multiple Choice");
////			}
////		  });
//		  
//		  JFileChooserTester tester = new JFileChooserTester();
//		  tester.actionSelectMenuItem(v.getSearchMc());
//		  tester.actionClick(v.getSearchMc());
//		  tester.actionSetFilename(fc, filepath);
//		  
////		  fc.setSelectedFile(new File(filepath));
////	  fc.setApproveButtonMnemonic(JFileChooser.APPROVE_OPTION);
//		  Mockito.verify(c).onChangeMCFilePath(filepath); }
//	  
//	  @Test public void setFileTf() { 
//		  ActionEvent e = new ActionEvent(v.getSearchTf(), ActionEvent.ACTION_PERFORMED, ""); 
//		  JFileChooser fc = v.getFcTf(); 
//		  String filepath = "C:\\file\\qualsiasi";
////		  fc.setSelectedFile(new File(filepath));
////		  fc.setApproveButtonMnemonic(JFileChooser.APPROVE_OPTION);
//		  v.actionPerformed(e); 
//		  Mockito.verify(c).onChangeTFFilePath(filepath); 
//	  }
	 
	 
}
