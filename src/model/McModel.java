package model;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;

public class McModel extends Model{

	private static final String FIRST_KEY = "\"MC\"";
	private static final String[] MC_KEYS = {"category","question",
			"A", "B", "C", "D", "answer", "caption"};
	
	public McModel(String filename) throws FileNotFoundException{
		super(filename, FIRST_KEY, MC_KEYS);
	}

	
	@Override
	public IAnswers[] readAnswers(String category_search) throws FileNotFoundException, IOException {
		//argument error check
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
	    int line_i = 1;
	    while ((line = br.readLine()) != null) {
	       String[] words = splitLine(line);
	       String category_in_file = words[0];
	       if (category_search.isEmpty() 
	    		   || category_search.equals(category_in_file)) {
	    	   //Questions
	    	   String question = words[1];
	    	   String A = words[2];
	    	   String B = words[3];
	    	   String C = words[4];
	    	   String D = words[5];
	    	   String correctAnswer = words[6];
	    	   String caption = words[7];
	    	   //create answer and add to list
	    	   AnswerMC a = new AnswerMC(line_i, category_in_file, question, A, B, C, D, correctAnswer, caption);
	    	   answer_list.add(a);
	       }
	       line_i++;
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
	public boolean removeWrongLines() throws FileNotFoundException, IOException {
		
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
		    boolean ok_line = splittedLine.length == MC_KEYS.length && (splittedLine[6].equals("A") || splittedLine[6].equals("B") ||
		    		splittedLine[6].equals("C") || splittedLine[6].equals("D"));
		    
		    if(!ok_line) {	//se non è ok, skip la riga
		    	removed = true;
		    }else { //altrimenti scrivi nel nuovo file
		    	assert ok_line;
//		    	System.out.println(currentLine);
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
	       if (words.length != FIELDS.length || (!words[6].equals("A") && !words[6].equals("B") 
	    		   && !words[6].equals("C") && !words[6].equals("D"))){
	    	   br.close();
	    	   return true;
	       }
	    }
		br.close();
		return false;
	}
		
}
