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
			"A", "B", "C", "D", "correct answer", "caption"};
	
	public McModel(String filename) throws FileNotFoundException{
		super(filename, FIRST_KEY, MC_KEYS);
	}

	@Override
	public IAnswers[] readAnswers(String category_search) throws FileNotFoundException, IOException {
		File file = new File(filename);
		if (category_search == null) {
			throw new IllegalArgumentException("la stringa di ricerca è null");
		}
		int num_answers = (int) (file.length() - 1);
		//se è vuoto
		if (num_answers <= 0) {
			return null; 
		}
		ArrayList<AnswerMC> answer_list = new ArrayList<AnswerMC>();
		String line;
		BufferedReader br = new BufferedReader(new FileReader(new File(filename)));
	    //skip first lines
	    br.readLine();
	    br.readLine();
	    //search new line
	    while ((line = br.readLine()) != null) {
	       String[] words = splitLine(line);
	       String category = words[0];
	       if (category_search!=null && category_search.isEmpty() 
	    		   && category_search.equals(category)) {
	    	   //Questions
	    	   String category_s = words[0];
	    	   String question = words[1];
	    	   String A = words[2];
	    	   String B = words[3];
	    	   String C = words[4];
	    	   String D = words[5];
	    	   String correctAnswer = words[6];
	    	   String caption = words[7];
	    	   
	    	   AnswerMC a = new AnswerMC(category_s, question, A, B, C, D, correctAnswer, caption);
	    	   answer_list.add(a);
	       }
	    }

		if (answer_list==null || answer_list.isEmpty()) {
			return null;
		}else {
			return (IAnswers[]) answer_list.toArray();
		}
		
	}

	@Override
	public boolean removeWrongLines() throws FileNotFoundException, IOException {
		File inputFile = new File(filename);
		File tempFile = new File("myTempFile.txt");

		BufferedReader reader = new BufferedReader(new FileReader(inputFile));
		BufferedWriter writer = new BufferedWriter(new FileWriter(tempFile));

		String currentLine;
		while((currentLine = reader.readLine()) != null) {
		    // trim newline when comparing with lineToRemove
		    String trimmedLine = currentLine.trim();
		    String[] splittedLine = splitLine(trimmedLine);
		    boolean ok_line = splittedLine.length == MC_KEYS.length && (splittedLine[6].equals("A") || splittedLine[6].equals("B") ||
		    		splittedLine[6].equals("C") || splittedLine[6].equals("D"));
		    if(!ok_line) continue;
		    assert ok_line;
		    writer.write(currentLine + System.getProperty("line.separator"));
		}
		writer.close(); 
		reader.close(); 
		boolean successful = tempFile.renameTo(inputFile);
		return successful;
	}

		
}
