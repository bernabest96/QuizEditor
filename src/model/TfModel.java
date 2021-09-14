package model;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.ObjectInputStream.GetField;
import java.util.ArrayList;

public class TfModel extends Model {
	
	private static final String TF_KEY = "\"TF\"";
	private static final String[] TF_FIELDS = {"category", "question", "correct answer", "caption"};

	public TfModel(String filename) throws FileNotFoundException {
		super(filename, TF_KEY, TF_FIELDS);
	}

	@Override
	public IAnswers[] readAnswers(String category_search) throws FileNotFoundException, IOException {
		File file = new File(filename);
		if (category_search == null) {
			throw new IllegalArgumentException("la stringa di ricerca è null");
		}
		int num_answers = (int) (file.length() - 1);
		if (num_answers <= 0 || !file.exists()) {
			return null; 
		}
		ArrayList<AnswerTF> answer_list = new ArrayList<>();
		String line;
		BufferedReader br = new BufferedReader(new FileReader(new File(filename)));
	    //skip first lines
	    br.readLine();
	    br.readLine();
	    //search new line
	    while ((line = br.readLine()) != null) {
	       String[] words = splitLine(line);
	       String categoryy = words[0];
	       if (category_search!=null && category_search.isEmpty() 
	    		   && category_search.equals(category_search)) {
	    	   //Questions
	    	   String category_s = words[0];
	    	   String question = words[1];
	    	   String correctAnswer = words[2];
	    	   String caption = words[3];
	    	   boolean corrAns = correctAnswer.equals("t");
	    	   AnswerTF a = new AnswerTF(category_s, question, corrAns, caption);
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
	public boolean removeWrongLines() throws IOException {
		// TODO Auto-generated method stub
		return false;
	}

}
