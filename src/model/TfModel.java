package model;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream.GetField;
import java.util.ArrayList;

public class TfModel extends Model {
	
	private static final String TF_KEY = "\"TF\"";
	private static final String[] TF_FIELDS = {"category", "question", "answer", "caption"};

	public TfModel(String filename) throws FileNotFoundException {
		super(filename, TF_KEY, TF_FIELDS);
	}

	@Override
	public IAnswers[] readAnswers(String category_search) throws FileNotFoundException, IOException {
		//check input 
		if (category_search == null) {
			throw new IllegalArgumentException("la stringa di ricerca è null");
		}
		if (!this.isWellFormed()) {
			throw new IllegalArgumentException("Hai cercato di leggere quiz in un file di righe nel formato scorretto");
		}
		
		ArrayList<IAnswers> answer_list = new ArrayList<IAnswers>();
		String line;
		BufferedReader br = new BufferedReader(new FileReader(new File(filename)));
	    //skip first lines
	    br.readLine();
	    br.readLine();
	    //search new line
	    while ((line = br.readLine()) != null) {
	       String[] words = splitLine(line);
	       String category_in_file = words[0];
	       if (category_search.isEmpty() 
	    		   || category_search.equals(category_in_file)) {
	    	   //Questions
	    	   String category_s = words[0];
	    	   String question = words[1];
	    	   String correctAnswer = words[2];
	    	   String caption = words[3];
	    	   boolean corrAns = correctAnswer.equals("t");
	    	   IAnswers a = new AnswerTF(category_s, question, corrAns, caption);
	    	   answer_list.add(a);
	       }
	    }

	    br.close();
		if (answer_list.isEmpty()) {
			//vuoto o non trova la stringa di ricerca
			return null;
		}else {
			//assert
			assert !answer_list.isEmpty();
			//conversione da lista a array
			Object[] obj_list = answer_list.toArray();
			//assert
			assert obj_list != null && obj_list.length > 0;
			IAnswers[] answ_list = new IAnswers[obj_list.length];
			for (int i=0; i < obj_list.length; i++) {
				answ_list[i] = (IAnswers) obj_list[i];
			}
			return answ_list;
		}
		
	}

	@Override
	public boolean removeWrongLines() throws IOException {
		//check input correct
		if (!this.hasKeyWords()) {
			throw new IllegalArgumentException("Il file deve essere ben formato! this.hasKeyWords() == false");
		}
		//Rimuovi
		File inputFile = new File(filename);
		File tempFile = new File("myTempFile.txt");

		BufferedReader reader = new BufferedReader(new FileReader(inputFile));
		BufferedWriter writer = new BufferedWriter(new FileWriter(tempFile));
		
		//riporta le prime due
		writer.write(reader.readLine() + System.lineSeparator()); 
		writer.write(reader.readLine() + System.lineSeparator()); 
		
		boolean removed = false;
		String currentLine;
		while((currentLine = reader.readLine()) != null) {
		    String[] splittedLine = splitLine(currentLine);
		    boolean ok_line = splittedLine.length == TF_FIELDS.length && (splittedLine[2].equals("t") || splittedLine[2].equals("f"));
		    
		    if(!ok_line) {	//se non è ok, skip la riga
		    	removed = true;
		    }else { //altrimenti scrivi nel nuovo file
		    	assert ok_line;
//				    	System.out.println(currentLine);
			    writer.write(currentLine + System.lineSeparator());
			    writer.flush();
		    }
		    
		}
		writer.close(); 
		reader.close();
		//problema
		boolean deleted = inputFile.delete();
		boolean renamed = tempFile.renameTo(inputFile);
		return removed && deleted && renamed;
	}

	@Override
	public boolean hasWrongLines() throws FileNotFoundException, IOException {
		BufferedReader br = new BufferedReader(new FileReader(new File(filename)));
		//Skip two lines
		br.readLine();
		br.readLine();
		//cycle over file
		String line;
		while ((line = br.readLine()) != null) {
	       String[] words = splitLine(line);
	       if (words.length != FIELDS.length || (!words[2].equals("t") && !words[2].equals("f"))){
	    	   br.close();
	    	   return true;
	       }
	    }
		br.close();
		return false;
	}
	
	

}
