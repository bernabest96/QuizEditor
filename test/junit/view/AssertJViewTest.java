package junit.view;

import java.awt.Component;

import java.awt.Dimension;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.InputEvent;

import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JRadioButton;

import org.junit.Test;

import abbot.finder.ComponentNotFoundException;
import abbot.finder.Matcher;
import abbot.finder.MultipleComponentsFoundException;
import abbot.finder.matchers.ClassMatcher;
import abbot.tester.ComponentLocation;
import abbot.tester.ComponentTester;
import abbot.tester.JButtonTester;
import abbot.tester.JComponentTester;
import abbot.tester.JFileChooserTester;
import abbot.tester.JLabelTester;
import abbot.tester.JTextComponentTester;
import abbot.tester.Robot;
import controller.IController;
import junit.extensions.abbot.ComponentTestFixture;
import junit.extensions.abbot.TestHelper;
import nz.ac.waikato.modeljunit.Tester;
import view.View;

public class AssertJViewTest extends ComponentTestFixture{

	public static void main(String[] args) {
		TestHelper.runTests(args, AssertJViewTest.class);
	}
	
	public void test() throws ComponentNotFoundException, MultipleComponentsFoundException {
		// Suppose MyComponent has a text field and a button...
	    MyComponent comp = new MyComponent();
	    // Display a frame containing the given component
	    showFrame(comp);
	    
	    JButton button = (JButton) getFinder().find(comp, new ClassMatcher(JButton.class));
        JLabel l = (JLabel) getFinder().find(comp, new ClassMatcher(JLabel.class));
        
//        tester.actionEnterText(textField, "This text is typed in the text field");
//        tester.actionClick(button);
        // Perform some tests on the state of your UI or model
        assertEquals("test iniziale label", "Label di prova", l.getText());
        assertEquals("test iniziale button", "OK", button.getText());
        
        JButtonTester t = new JButtonTester();
        
        t.actionDelay(1000);
//        button.doClick();
//        r.mousePress(InputEvent.BUTTON1_MASK);
//        r.mouseRelease(InputEvent.BUTTON1_MASK);
//        t.actionActionMap(button, "actionPerformed");
        t.mouseMove(button);
        t.actionClick(button);
        t.actionDelay(1000);
        assertEquals("Fallito il cambiamenti","NO", l.getText());
	}
	
//	@Test
//	public void test02() throws ComponentNotFoundException, MultipleComponentsFoundException{
//		
//	}
	
//	@Mock
//	IController c;
//	
//	@InjectMocks
//	View v;
//	
//	@Before
//	public void setup() {
//		v = new View();
//		assertNotNull(c);
//		v.registerListener(c);
//	}
	
	
	
	
//	@Test
	public void test02() throws ComponentNotFoundException, MultipleComponentsFoundException {
		View v = new View();
		
		JButtonTester tester = new JButtonTester();
        
        JButton button = (JButton) getFinder().find(v, new Matcher() {
			
			@Override
			public boolean matches(Component c) {
				// TODO Auto-generated method stub
				return c instanceof JButton && ((JButton) c).getText().equals("Insert!");
			}
		});
//        button.doClick();
//        tester.actionDelay(1000);
//        tester.mouseMove(button);
        tester.actionDelay(1000);
        tester.actionMouseMove(button, new ComponentLocation(new Point(0, 0)));
        tester.actionClick(button);
        tester.actionDelay(1000);
	}
	
	
	/*
	 * public void test03() throws ComponentNotFoundException,
	 * MultipleComponentsFoundException { View v = new View();
	 * 
	 * JButtonTester tester = new JButtonTester(); ComponentTester t =
	 * ComponentTester.getTester(JRadioButton.class);
	 * 
	 * JButton button = (JButton) getFinder().find(v, new Matcher() {
	 * 
	 * @Override public boolean matches(Component c) { // TODO Auto-generated method
	 * stub return c instanceof JButton && ((JButton)
	 * c).getText().equals("Search!"); } });
	 * 
	 * JRadioButton rb = (JRadioButton) getFinder().find(v, new Matcher() {
	 * 
	 * @Override public boolean matches(Component c) { // TODO Auto-generated method
	 * stub return c instanceof JRadioButton && ((JRadioButton)
	 * c).getText().equals("Insert!"); } }); // button.doClick(); //
	 * tester.actionDelay(1000); // tester.mouseMove(button);
	 * tester.actionDelay(1000); tester.actionMouseMove(button, null);
	 * tester.actionClick(button); tester.actionDelay(1000); }
	 */
	 

}
