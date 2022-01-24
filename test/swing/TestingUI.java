package swing;

import java.awt.BorderLayout;
import java.awt.CardLayout;
import java.awt.Color;
import java.awt.Container;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.Queue;

import javax.swing.*;
import javax.swing.text.AbstractDocument.Content;

import view.CustomQueue;
import view.ICustomQueue;

public class TestingUI extends JFrame implements ActionListener{

	private static final int WIDTH_W = 700;
	private static final int HEIGHT_W = 1000;
	private static final int MAX_LINE_IN_MEMORY = 50;
	private ICustomQueue queue;
	
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
	
	/*------------*/
	
	public TestingUI() {
		queue = new CustomQueue(MAX_LINE_IN_MEMORY);
		setTitle("Testing Swing");
		
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
		AField = new JTextField();
		BField = new JTextField();
		CField = new JTextField();
		DField = new JTextField();
		captionMCField = new JTextArea("captionMC");
		JLabel captionLabel01 = new JLabel("Caption:");
		ARadioButton = new JRadioButton("A)");
		BRadioButton = new JRadioButton("B)");
		CRadioButton = new JRadioButton("C)");
		DRadioButton = new JRadioButton("D)");
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
		falseRB = new JRadioButton("False");
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
		
		//set JFrame operation
		setDefaultCloseOperation(EXIT_ON_CLOSE);
		pack();
		setVisible(true);
		
	}
	
	public static void main(String[] args) {
		new TestingUI();
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		Object obj = e.getSource();
		//menu
		if (obj == searchMc) {
			JFileChooser fc=new JFileChooser();    
		    int i=fc.showOpenDialog(this);    
		    if(i==JFileChooser.APPROVE_OPTION){    
		        File f=fc.getSelectedFile();    
		        String filepath=f.getPath(); 
		        displayError.setText("filename : " + filepath);
//		        displayError.setText("Ciao pippo!");
		    }
		}
		
		
		
		//insert switch logic
		if (obj == insertRB) {
			if (searchRB.isSelected()) {
				for (int i=0; i<100; i++) {
					queue.enqueue("Premuto insert: " + i);
				}
				//displayError.setText("");
				displayError.setText(queue.toString());
				contentCard.next(contentPanel);	
			}
			insertRB.setSelected(true);
			searchRB.setSelected(false);
			
		}else if (obj == searchRB) {
			if (insertRB.isSelected()) {
				queue.enqueue("Premuto search");
				//displayError.setText("");
				displayError.setText(queue.toString());
				contentCard.next(contentPanel);
			}
			searchRB.setSelected(true);
			insertRB.setSelected(false);
			
		}
		//mc-tf
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
		
		//search test
		if (obj == searchButton) {
			String text = "";
			for (int i=0; i<100; i++) {
				text += "Questa frase è falsa : " + i + "\n";
			}
			displayQuiz.setText(text);
			
		}
			
	}
	
}
