package view;

import static org.junit.Assume.assumeFalse;

import java.awt.BorderLayout;
import java.awt.CardLayout;
import java.awt.Container;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;

import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;

import controller.Controller;
import controller.IController;
import model.IAnswers;

public class View extends JFrame implements IView, ActionListener{

	private /* spec_public */ IController controller;
	private String currentMCFilePath;
	private String currentTFFilePath;
	private CustomQueue quizMessages;
	private CustomQueue infoErrorMessages;
	private static final int MAX_LINE_QUIZ_MEX = 50;
	private static final int MAX_LINE_INFO_MEX = 200;
	
	
	/**************SWING**********************************/
	//Swing fields
	private static final String TITLE = "Quiz Editor";
	private static final int WIDTH_W = 700;
	private static final int HEIGHT_W = 1000;
	
	//menu
	JMenuBar bar;
	JMenu menu;
	JMenuItem searchMc, searchTf;
	//radiobutton
	JRadioButton insertRB;
	JRadioButton searchRB;
	JRadioButton mcRB;
	JRadioButton tfRB;
	
	
	JPanel insertOrSearchPanel;
	JPanel contentPanel;
	JPanel errorPanel;
	JPanel menuPanel;
	
	/*------------*/
	
	//Multiple Choice
	JPanel mcPanel;
	JTextField categoryMCField;
	JTextArea questionMCField;
	JTextField AField, BField, CField, DField;
	JRadioButton ARadioButton, BRadioButton, CRadioButton, DRadioButton;
	JTextArea captionMCField;
	JButton insertMCButton, insertTFButton;
	//True False
	JTextField categoryTFField;
	JPanel tfPanel;
	JTextArea questionTFField;
	JRadioButton trueRB, falseRB;
	JLabel trueLabel, falseLabel;
	JTextArea captionTFField;
	
	/*------------*/
	JTextArea displayError;
	JScrollPane scrollError;
	
	CardLayout mctfCard, contentCard;
	JPanel searchPanel, insertPanel;
	
	/*------------*/
	//SEARCH
	JRadioButton mcS, tfS;
	JTextField categoryText;
	JTextArea displayQuiz;
	JScrollPane scrollQuiz;
	JButton searchButton;
	private JFileChooser fcMc;
	private JFileChooser fcTf;
	
	/*------------*/
	/**********************************************************/
	
	public View() {
		//inizializza il resto
		controller = null;
		currentMCFilePath = "";
		currentTFFilePath = "";
		quizMessages = new CustomQueue(MAX_LINE_QUIZ_MEX);
		infoErrorMessages = new CustomQueue(MAX_LINE_INFO_MEX);
		
		
		/*----------------------SWING------------------------*/
		//Swing
		setTitle(TITLE);
		
		/*----------------------------------------------*/
		//panel
		Container c = getContentPane();
		
		insertOrSearchPanel = new JPanel();
		contentPanel = new JPanel();
		errorPanel = new JPanel();
		
		GridBagLayout grid01 = new GridBagLayout();
		GridBagConstraints gbc01 = new GridBagConstraints();
		c.setLayout(grid01);
		
		gbc01.fill = GridBagConstraints.HORIZONTAL;  
		gbc01.gridx = 0;  
		gbc01.gridy = 0; 
		gbc01.ipady = 20;
		gbc01.ipadx = 300;
		c.add(insertOrSearchPanel, gbc01);
	    gbc01.fill = GridBagConstraints.HORIZONTAL;  
	    gbc01.ipady = 200;  
	    gbc01.gridx = 0;
	    gbc01.gridy = 1;
	    //gbc.ipadx = 100;
	    c.add(contentPanel, gbc01);
	    gbc01.fill = GridBagConstraints.HORIZONTAL; 
	    gbc01.ipady = 200;  
	    gbc01.gridx = 0;  
	    gbc01.gridy = 2;
	    //gbc.ipadx = 100;
	    c.add(errorPanel, gbc01);
		
		/*-----------------------------------------------*/
		//menu
		bar = new JMenuBar();
		menu = new JMenu("File");
		searchMc = new JMenuItem("Choose File for Multiple Choice");
		searchTf = new JMenuItem("Choose File for True False");
		searchMc.addActionListener(this);
		searchTf.addActionListener(this);
		menu.add(searchMc);
		menu.add(searchTf);
		bar.add(menu);
		setJMenuBar(bar);
		
		/*------------------------------------------------*/
		//insert
		insertRB = new JRadioButton("Insert", true);
		searchRB = new JRadioButton("Search", false);
		mcRB = new JRadioButton("Mc", true);
		tfRB = new JRadioButton("Tf", false);
		
		GridLayout gridLayout2 = new GridLayout(2, 2);
		insertOrSearchPanel.setLayout(gridLayout2);
		insertOrSearchPanel.add(insertRB);
		insertOrSearchPanel.add(searchRB);
		insertOrSearchPanel.add(mcRB);
		insertOrSearchPanel.add(tfRB);
		
		/*---------------------------*/
		//card layout and content panel
		contentCard = new CardLayout();
		insertPanel = new JPanel();
		searchPanel = new JPanel();
		mctfCard = new CardLayout();
		mcPanel = new JPanel();
		tfPanel = new JPanel();
		
		//Multiple Choice
		categoryMCField = new JTextField("Enter Category MC Here");
		JLabel categoryLabel01 = new JLabel("Category:");
		questionMCField = new JTextArea("Enter MC Question Here");
		JLabel questionLabel01 = new JLabel("Question:");
		AField = new JTextField("Enter Answer A");
		BField = new JTextField("Enter Answer B");
		CField = new JTextField("Enter Answer C");
		DField = new JTextField("Enter Answer D");
		captionMCField = new JTextArea("Enter caption for MC");
		JLabel captionLabel01 = new JLabel("Caption:");
		ARadioButton = new JRadioButton("A)"); ARadioButton.setSelected(true);
		BRadioButton = new JRadioButton("B)"); BRadioButton.setSelected(false);
		CRadioButton = new JRadioButton("C)"); CRadioButton.setSelected(false);
		DRadioButton = new JRadioButton("D)"); DRadioButton.setSelected(false);
		insertMCButton = new JButton("Insert!");
		
		
		GridBagLayout grid02 = new GridBagLayout();
		GridBagConstraints gbc02 = new GridBagConstraints();
		mcPanel.setLayout(grid02);
		
		gbc02.fill = GridBagConstraints.HORIZONTAL;  
		gbc02.gridx = 0;  
		gbc02.gridy = 0; 
		gbc02.ipady = 20;
		gbc02.ipadx = 50;
		mcPanel.add(categoryLabel01, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL;  
	    gbc02.ipady = 20;  
	    gbc02.gridx = 1;
	    gbc02.gridy = 0;
	    gbc02.ipadx = 250;
	    mcPanel.add(categoryMCField, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL; 
	    gbc02.ipady = 20;  
	    gbc02.gridx = 0;  
	    gbc02.gridy = 1;
	    gbc02.ipadx = 50;
	    mcPanel.add(questionLabel01, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL; 
	    gbc02.ipady = 50;  
	    gbc02.gridx = 1;  
	    gbc02.gridy = 1;
	    gbc02.ipadx = 250;
	    mcPanel.add(questionMCField, gbc02);
	    //A, B, C, D
	    gbc02.fill = GridBagConstraints.HORIZONTAL;  
		gbc02.gridx = 0;  
		gbc02.gridy = 2; 
		gbc02.ipady = 20;
		gbc02.ipadx = 50;
		mcPanel.add(ARadioButton, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL;  
	    gbc02.ipady = 20;  
	    gbc02.gridx = 1;
	    gbc02.gridy = 2;
	    gbc02.ipadx = 250;
	    mcPanel.add(AField, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL; 
	    gbc02.ipady = 20;  
	    gbc02.gridx = 0;  
	    gbc02.gridy = 3;
	    gbc02.ipadx = 50;
	    mcPanel.add(BRadioButton, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL; 
	    gbc02.ipady = 20;  
	    gbc02.gridx = 1;  
	    gbc02.gridy = 3;
	    gbc02.ipadx = 250;
	    mcPanel.add(BField, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL;  
		gbc02.gridx = 0;  
		gbc02.gridy = 4; 
		gbc02.ipady = 20;
		gbc02.ipadx = 50;
		mcPanel.add(CRadioButton, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL;  
	    gbc02.ipady = 20;  
	    gbc02.gridx = 1;
	    gbc02.gridy = 4;
	    gbc02.ipadx = 250;
	    mcPanel.add(CField, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL; 
	    gbc02.ipady = 20;  
	    gbc02.gridx = 0;  
	    gbc02.gridy = 5;
	    gbc02.ipadx = 50;
	    mcPanel.add(DRadioButton, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL; 
	    gbc02.ipady = 20;  
	    gbc02.gridx = 1;  
	    gbc02.gridy = 5;
	    gbc02.ipadx = 250;
	    mcPanel.add(DField, gbc02);
	    
	    gbc02.fill = GridBagConstraints.HORIZONTAL; 
	    gbc02.ipady = 20;  
	    gbc02.gridx = 0;  
	    gbc02.gridy = 6;
	    gbc02.ipadx = 50;
	    mcPanel.add(captionLabel01, gbc02);
	    gbc02.fill = GridBagConstraints.HORIZONTAL; 
	    gbc02.ipady = 50;  
	    gbc02.gridx = 1;  
	    gbc02.gridy = 6;
	    gbc02.ipadx = 250;
	    mcPanel.add(captionMCField, gbc02);
	    
	    gbc02.fill = GridBagConstraints.HORIZONTAL; 
	    gbc02.ipady = 20;  
	    gbc02.gridx = 0;  
	    gbc02.gridy = 7;
	    gbc02.gridwidth = 2;
	    gbc02.ipadx = 300;
	    mcPanel.add(insertMCButton, gbc02);
		
		//Tf
	    categoryTFField = new JTextField("Enter categoty Tf Here");
		JLabel categoryLabel02 = new JLabel("Category:");
	    questionTFField = new JTextArea("Enter TF Question Here");
		JLabel questionLabel02 = new JLabel("Question:");
	    trueRB = new JRadioButton("True");
	    trueRB.setSelected(true);
		falseRB = new JRadioButton("False");
		falseRB.setSelected(false);
		trueLabel = new JLabel("True");
		falseLabel = new JLabel("False");
		captionTFField = new JTextArea("caption tf");
		JLabel captionLabel02 = new JLabel("Caption:");
		insertTFButton = new JButton("Insert!");
		
		
		GridBagLayout grid03 = new GridBagLayout();
		GridBagConstraints gbc03 = new GridBagConstraints();
		tfPanel.setLayout(grid03);
		
		gbc03.fill = GridBagConstraints.HORIZONTAL;  
		gbc03.gridx = 0;  
		gbc03.gridy = 0; 
		gbc03.ipady = 20;
		gbc03.ipadx = 50;
		tfPanel.add(categoryLabel02, gbc03);
	    gbc03.fill = GridBagConstraints.HORIZONTAL;  
	    gbc03.ipady = 20;  
	    gbc03.gridx = 1;
	    gbc03.gridy = 0;
	    gbc03.ipadx = 250;
	    tfPanel.add(categoryTFField, gbc03);
	    gbc03.fill = GridBagConstraints.HORIZONTAL;  
		gbc03.gridx = 0;  
		gbc03.gridy = 1; 
		gbc03.ipady = 20;
		gbc03.ipadx = 50;
		tfPanel.add(questionLabel02, gbc03);
	    gbc03.fill = GridBagConstraints.HORIZONTAL;  
	    gbc03.ipady = 20;  
	    gbc03.gridx = 1;
	    gbc03.gridy = 1;
	    gbc03.ipadx = 250;
	    tfPanel.add(questionTFField, gbc03);
	    
	    gbc03.fill = GridBagConstraints.HORIZONTAL;  
		gbc03.gridx = 0;  
		gbc03.gridy = 2; 
		gbc03.ipady = 20;
		gbc03.ipadx = 50;
		gbc03.gridwidth = 2;
		tfPanel.add(trueRB, gbc03);
	    gbc03.fill = GridBagConstraints.HORIZONTAL; 
	    gbc03.ipady = 20;  
	    gbc03.gridx = 0;  
	    gbc03.gridy = 3;
	    gbc03.ipadx = 50;
	    gbc03.gridwidth = 2;
	    tfPanel.add(falseRB, gbc03);
	    
	    gbc03.fill = GridBagConstraints.HORIZONTAL;  
		gbc03.gridx = 0;  
		gbc03.gridy = 4; 
		gbc03.ipady = 20;
		gbc03.ipadx = 50;
		tfPanel.add(captionLabel02, gbc03);
	    gbc03.fill = GridBagConstraints.HORIZONTAL;  
	    gbc03.ipady = 50;  
	    gbc03.gridx = 1;
	    gbc03.gridy = 4;
	    gbc03.ipadx = 250;
	    tfPanel.add(captionTFField, gbc03);
	    
	    gbc03.fill = GridBagConstraints.HORIZONTAL;  
		gbc03.gridx = 0;  
		gbc03.gridy = 5; 
		gbc03.ipady = 20;
		gbc03.ipadx = 300;
		gbc03.gridwidth = 2;
		tfPanel.add(insertTFButton, gbc03);
		
		
		//carl loyout for insert panel
		insertPanel.setLayout(mctfCard);
		insertPanel.add(mcPanel);
		insertPanel.add(tfPanel);
		
		//SEARCH
		categoryText = new JTextField();
		displayQuiz = new JTextArea("DisplayQuiz");
		displayQuiz.setEditable(false);
		scrollQuiz = new JScrollPane(displayQuiz);
		searchButton = new JButton("Search!");
		JLabel categoryLabel03 = new JLabel("Category:");
		
		GridBagLayout grid04 = new GridBagLayout();
		GridBagConstraints gbc04 = new GridBagConstraints();
		searchPanel.setLayout(grid04);
		
		gbc04.fill = GridBagConstraints.HORIZONTAL;  
		gbc04.gridx = 0;  
		gbc04.gridy = 0; 
		gbc04.ipady = 20;
		gbc04.ipadx = 50;
		searchPanel.add(categoryLabel03, gbc04);
	    gbc04.fill = GridBagConstraints.HORIZONTAL;  
	    gbc04.ipady = 20;  
	    gbc04.gridx = 1;
	    gbc04.gridy = 0;
	    gbc04.ipadx = 250;
	    searchPanel.add(categoryText, gbc04);
	    gbc04.fill = GridBagConstraints.HORIZONTAL;  
		gbc04.gridx = 0;  
		gbc04.gridy = 1; 
		gbc04.ipady = 300;
		gbc04.ipadx = 300;
		gbc04.gridwidth = 2;
		searchPanel.add(scrollQuiz, gbc04);
		gbc04.fill = GridBagConstraints.HORIZONTAL;  
		gbc04.ipady = 20;  
	    gbc04.gridx = 0;
	    gbc04.gridy = 2;
	    gbc04.ipadx = 300;
	    searchPanel.add(searchButton, gbc04);

		
		//content panel
		contentPanel.setLayout(contentCard);
		contentPanel.add(insertPanel);
		contentPanel.add(searchPanel);
		/*----------------------------*/
		//display error panel
		displayError = new JTextArea("Non editabile");
		scrollError = new JScrollPane(displayError);
		displayError.setEditable(false);
		errorPanel.setLayout(new BorderLayout());
		errorPanel.add(scrollError, BorderLayout.CENTER);
		
		/*-----------------------------*/
		//add listeners
		insertRB.addActionListener(this);
		searchRB.addActionListener(this);
		mcRB.addActionListener(this);
		tfRB.addActionListener(this);
		searchButton.addActionListener(this);
		insertTFButton.addActionListener(this);
		insertMCButton.addActionListener(this);
		ARadioButton.addActionListener(this);
		BRadioButton.addActionListener(this);
		CRadioButton.addActionListener(this);
		DRadioButton.addActionListener(this);
		trueRB.addActionListener(this);
		falseRB.addActionListener(this);
		
		//set JFrame operation
		setDefaultCloseOperation(EXIT_ON_CLOSE);
		pack();
		setVisible(true);
		fcMc = new JFileChooser();
		fcTf = new JFileChooser();
	}

	// also ensures \result.length == 2;
	@Override
	public String[] getSelectedAnswer() {
		String[] files = new String[] {currentMCFilePath, currentTFFilePath};
		return files;
	}

	public JRadioButton getInsertRB() {
		return insertRB;
	}

	public JRadioButton getSearchRB() {
		return searchRB;
	}

	public JRadioButton getMcRB() {
		return mcRB;
	}

	public JRadioButton getTfRB() {
		return tfRB;
	}

	public JRadioButton getARadioButton() {
		return ARadioButton;
	}

	public JRadioButton getBRadioButton() {
		return BRadioButton;
	}

	public JRadioButton getCRadioButton() {
		return CRadioButton;
	}

	public JRadioButton getDRadioButton() {
		return DRadioButton;
	}

	// also ensures this.controller != null;
	@Override
	public void registerListener(/*@ non_null @*/IController controller) {
		if (controller == null)	throw new IllegalArgumentException("Valore nullo");
		this.controller = controller;
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		//difensivo
		assert controller != null : "Non hai registrato il controller alla view";
		
		Object obj = e.getSource();
		
		//menu search MC
		if (obj == searchMc) {
			int i=fcMc.showOpenDialog(this);    
		    if(i==JFileChooser.APPROVE_OPTION){    
		        File f=fcMc.getSelectedFile();    
		        currentMCFilePath = f.getPath();
		        controller.onChangeMCFilePath(currentMCFilePath);
		    }
		}
		//menu search TF
		if (obj == searchTf) {
			int i=fcTf.showOpenDialog(this);    
		    if(i==JFileChooser.APPROVE_OPTION){
		        File f=fcTf.getSelectedFile();    
		        currentTFFilePath = f.getPath();
		        controller.onChangeTFFilePath(currentTFFilePath);
		    }
		}
		
		//insert search switch logic
		if (obj == insertRB) {
			if (searchRB.isSelected()) {
				//switch card layout
				contentCard.next(contentPanel);	
			}
			insertRB.setSelected(true);
			searchRB.setSelected(false);
			
		}else if (obj == searchRB) {
			if (insertRB.isSelected()) {
				//switch card layout
				contentCard.next(contentPanel);
			}
			searchRB.setSelected(true);
			insertRB.setSelected(false);
			
		}
		
		//mc-tf logic
		if (obj == mcRB) {
			if (tfRB.isSelected()) {
				mctfCard.next(insertPanel);
			}
			mcRB.setSelected(true);
			tfRB.setSelected(false);
			assert mcRB.isSelected();
		}else if (obj == tfRB) {
			if (mcRB.isSelected()) {
				mctfCard.next(insertPanel);
			}
			tfRB.setSelected(true);
			mcRB.setSelected(false);
			assert tfRB.isSelected();
		}
		
		//A-B-C-D switch
		if (obj == ARadioButton) {
			ARadioButton.setSelected(true);
			BRadioButton.setSelected(false);
			CRadioButton.setSelected(false);
			DRadioButton.setSelected(false);
		}else if (obj == BRadioButton) {
			ARadioButton.setSelected(false);
			BRadioButton.setSelected(true);
			CRadioButton.setSelected(false);
			DRadioButton.setSelected(false);
		}else if (obj == CRadioButton) {
			ARadioButton.setSelected(false);
			BRadioButton.setSelected(false);
			CRadioButton.setSelected(true);
			DRadioButton.setSelected(false);
		}else if (obj == DRadioButton) {
			ARadioButton.setSelected(false);
			BRadioButton.setSelected(false);
			CRadioButton.setSelected(false);
			DRadioButton.setSelected(true);
		}
		//true false switch
		if (obj == trueRB) {
			trueRB.setSelected(true);
			falseRB.setSelected(false);
		}else if (obj == falseRB) {
			trueRB.setSelected(false);
			falseRB.setSelected(true);
		}
		
		//invoke controller callback
		if (obj == insertMCButton) {
			//CALLBACK ON INSERT MC
			assert insertRB.isSelected() && mcRB.isSelected() && insertPanel.isEnabled() && mcPanel.isEnabled();
			String category = categoryMCField.getText();
			String question = questionMCField.getText();
			String[] answ = {AField.getText(), BField.getText(), CField.getText(), DField.getText()};
			String selectedAns = "";
			//ASSERT Solo uno deve essere selezionato.
			int a = ARadioButton.isSelected()? 1 : 0;
			int b = BRadioButton.isSelected()? 1 : 0;
			int c = CRadioButton.isSelected()? 1 : 0;
			int d = DRadioButton.isSelected()? 1 : 0;
			assert a + b + c + d == 1;
			//END ASSERT
			if (ARadioButton.isSelected()) {
				selectedAns = "A";
			}else if (BRadioButton.isSelected()) {
				selectedAns = "B";
			}else if (CRadioButton.isSelected()) {
				selectedAns = "C";
			}else if (DRadioButton.isSelected()) {
				selectedAns = "D";
			}
			String caption = captionMCField.getText();
			controller.onInsertMCButtonPressed(category, question, answ, selectedAns, caption);
		}else if (obj == insertTFButton) {
			//CALLBACK ON INSERT TF
			String category = categoryTFField.getText();
			String question = questionTFField.getText();
			//ASSERT
			//XOR
			assert trueRB.isSelected() ^ falseRB.isSelected();
			//ENDASSERT
			boolean truefalse = trueRB.isSelected()? true : false;
			String caption = captionTFField.getText();
			controller.onInsertTFButtonPressed(category, question, truefalse, caption);
		}else if (obj == searchButton) {
			String category = categoryText.getText();
			controller.onSearchButtonPressed(category);
		}
				
	}

	public JFileChooser getFcMc() {
		return fcMc;
	}

	public JFileChooser getFcTf() {
		return fcTf;
	}

	// also ensures \result != null;
	@Override
	public String getCategory() {
		return categoryText.getText();
	}

	//also ensures displayError.getText().split("\n")[displayError.getText().split("\n").length - 1].equals(message)
	@Override
	public void displayInfoErrorMessages(String message) {
		if (message == null) {
			throw new IllegalArgumentException("Valore nullo");
		}
		infoErrorMessages.enqueue(message);
		displayError.setText(infoErrorMessages.toString());
	}

	//also ensures displayQuiz.getText().split("\n")[displayQuiz.getText().split("\n").length - 1].equals(message)
	@Override
	public void displayQuizMessages(/*@ non_null @*/String message) {
		if (message == null) {
			throw new IllegalArgumentException("Valore nullo");
		}
		quizMessages.enqueue(message);
		displayQuiz.setText(quizMessages.toString());
	}

	/************FOR TESTING ONLY****************/
	public JMenuItem getSearchMc() {
		return searchMc;
	}

	public JMenuItem getSearchTf() {
		return searchTf;
	}
	public IController getController() {
		return controller;
	}

	public String getCurrentMCFilePath() {
		return currentMCFilePath;
	}

	public String getCurrentTFFilePath() {
		return currentTFFilePath;
	}

	public CustomQueue getQuizMessages() {
		return quizMessages;
	}

	public CustomQueue getInfoErrorMessages() {
		return infoErrorMessages;
	}

	public JMenuBar getBar() {
		return bar;
	}

	public JMenu getMenu() {
		return menu;
	}

	public JPanel getInsertOrSearchPanel() {
		return insertOrSearchPanel;
	}

	public JPanel getContentPanel() {
		return contentPanel;
	}

	public JPanel getErrorPanel() {
		return errorPanel;
	}

	public JPanel getMenuPanel() {
		return menuPanel;
	}

	public JPanel getMcPanel() {
		return mcPanel;
	}

	public JTextField getCategoryMCField() {
		return categoryMCField;
	}

	public JTextArea getQuestionMCField() {
		return questionMCField;
	}

	public JTextField getAField() {
		return AField;
	}

	public JTextField getBField() {
		return BField;
	}

	public JTextField getCField() {
		return CField;
	}

	public JTextField getDField() {
		return DField;
	}

	public JTextArea getCaptionMCField() {
		return captionMCField;
	}

	public JButton getInsertMCButton() {
		return insertMCButton;
	}

	public JButton getInsertTFButton() {
		return insertTFButton;
	}

	public JTextField getCategoryTFField() {
		return categoryTFField;
	}

	public JPanel getTfPanel() {
		return tfPanel;
	}

	public JTextArea getQuestionTFField() {
		return questionTFField;
	}

	public JRadioButton getTrueRB() {
		return trueRB;
	}

	public JRadioButton getFalseRB() {
		return falseRB;
	}

	public JLabel getTrueLabel() {
		return trueLabel;
	}

	public JLabel getFalseLabel() {
		return falseLabel;
	}

	public JTextArea getCaptionTFField() {
		return captionTFField;
	}

	public JTextArea getDisplayError() {
		return displayError;
	}

	public JScrollPane getScrollError() {
		return scrollError;
	}

	public CardLayout getMctfCard() {
		return mctfCard;
	}

	public CardLayout getContentCard() {
		return contentCard;
	}

	public JPanel getSearchPanel() {
		return searchPanel;
	}

	public JPanel getInsertPanel() {
		return insertPanel;
	}

	public JRadioButton getMcS() {
		return mcS;
	}

	public JRadioButton getTfS() {
		return tfS;
	}

	public JTextField getCategoryText() {
		return categoryText;
	}

	public JTextArea getDisplayQuiz() {
		return displayQuiz;
	}

	public JScrollPane getScrollQuiz() {
		return scrollQuiz;
	}

	public JButton getSearchButton() {
		return searchButton;
	}

}
