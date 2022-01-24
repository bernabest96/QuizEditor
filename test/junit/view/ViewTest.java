package junit.view;

import static org.junit.Assert.assertEquals;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.io.File;

import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JLabel;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.Mockito;
import org.mockito.junit.MockitoJUnit;
import org.mockito.junit.MockitoRule;
import org.mockito.runners.MockitoJUnit44Runner;
import org.mockito.runners.MockitoJUnitRunner;

import abbot.finder.ComponentNotFoundException;
import abbot.finder.Matcher;
import abbot.finder.MultipleComponentsFoundException;
import abbot.finder.matchers.ClassMatcher;
import abbot.tester.JButtonTester;
import abbot.tester.JComponentTester;
import controller.Controller;
import controller.IController;
import junit.extensions.abbot.ComponentTestFixture;
import nz.ac.waikato.modeljunit.gui.FileChooserFilter;
import view.View;

@RunWith(MockitoJUnit44Runner.class)
public class ViewTest{
	
	
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
	public void insertMC() {
		ActionEvent e = new ActionEvent(v.getInsertMCButton(), ActionEvent.ACTION_PERFORMED, "");
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
		v.actionPerformed(e);
		String[] ans = new String[] {risp_a, risp_b, risp_c, risp_d};
		Mockito.verify(c).onInsertMCButtonPressed(category, question, ans, "C", caption);
	}
	
	@Test
	public void insertTF() {
		ActionEvent e = new ActionEvent(v.getInsertTFButton(), ActionEvent.ACTION_PERFORMED, "");
		String category = "categoria_tf";
		v.getCategoryTFField().setText(category);
		String question = "La domanda su cosa?";
		v.getQuestionTFField().setText(question);
		v.getTrueRB().setSelected(false);
		v.getFalseRB().setSelected(true);
		String caption = "this is caption";
		v.getCaptionTFField().setText(caption);
		v.actionPerformed(e);
		Mockito.verify(c).onInsertTFButtonPressed(category, question, false, caption);
	}
	
	@Test
	public void search01() {
		ActionEvent e = new ActionEvent(v.getSearchButton(), ActionEvent.ACTION_PERFORMED, "");
		String category = "categoria_tf";
		v.getCategoryText().setText(category);
		v.actionPerformed(e);
		Mockito.verify(c).onSearchButtonPressed(category);
	}
	
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
	
	@Test
	public void display01() {
		String mex01 = "messaggio01";
		v.displayInfoErrorMessages(mex01);
//		System.out.println(unEscapeString(v.getDisplayError().getText()));
		assertEquals(mex01 + System.lineSeparator(), v.getDisplayError().getText());
		String mex02 = "messaggio02";
		v.displayInfoErrorMessages(mex02);
		String mex = mex01 + System.lineSeparator() + mex02 + System.lineSeparator();
//		System.out.println(mex);
		assertEquals( mex, v.getDisplayError().getText());
	}
	
	@Test
	public void insertMCPanel() {
		assertTrue(v.getMcPanel().isShowing());
	}
	
	@Test
	public void insertTfPanel() {
		ActionEvent e = new ActionEvent(v.getTfRB(), ActionEvent.ACTION_PERFORMED, "");
//		v.getTfRB().setSelected(true);
		v.actionPerformed(e);
		assertTrue(!v.getMcRB().isSelected());
		assertTrue(v.getTfRB().isSelected());
		assertTrue(!v.getMcPanel().isShowing());
		assertTrue(v.getTfPanel().isShowing());
	}
	
	@Test
	public void searchPanel() {
		ActionEvent e = new ActionEvent(v.getSearchRB(), ActionEvent.ACTION_PERFORMED, "");
//		v.getSearchRB().setSelected(true);
		v.actionPerformed(e);
		assertTrue(!v.getInsertRB().isSelected());
		assertTrue(v.getSearchRB().isSelected());
		assertTrue(v.getSearchPanel().isShowing());
		assertTrue(!v.getInsertPanel().isShowing());
	}
	
	/*
	 * @Test public void setFileMC() { ActionEvent e = new
	 * ActionEvent(v.getSearchMc(), ActionEvent.ACTION_PERFORMED, ""); JFileChooser
	 * fc = v.getFcMc(); String filepath = "C:\\file\\qualsiasi";
	 * fc.setSelectedFile(new File(filepath));
	 * fc.setApproveButtonMnemonic(JFileChooser.APPROVE_OPTION);
	 * v.actionPerformed(e); Mockito.verify(c).onChangeMCFilePath(filepath); }
	 * 
	 * @Test public void setFileTf() { ActionEvent e = new
	 * ActionEvent(v.getSearchTf(), ActionEvent.ACTION_PERFORMED, ""); JFileChooser
	 * fc = v.getFcTf(); String filepath = "C:\\file\\qualsiasi";
	 * fc.setSelectedFile(new File(filepath));
	 * fc.setApproveButtonMnemonic(JFileChooser.APPROVE_OPTION);
	 * v.actionPerformed(e); Mockito.verify(c).onChangeTFFilePath(filepath); }
	 */
	
	
}
