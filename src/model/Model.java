package model;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;

public abstract class Model implements IModel {

	protected /*@ spec_public @*/ String filename;
	protected String MAGIC_KEY;
	protected String[] FIELDS;
	
	public Model(String filename, String key, String[] keys) throws FileNotFoundException {
		if (filename == null) {
			throw new IllegalArgumentException("Valore nullo");
		}
		this.filename = filename;
		File file = new File(filename);
		if (!file.exists()) {
			throw new FileNotFoundException();
		}
		this.MAGIC_KEY = key;
		this.FIELDS = keys;
	}
	
	/*@  also
	  @  public normal_behavior
	  @  requires filename != null && (new File(filename)).exists();
	  @  ensures this.filename != null;
	  @	 also
	  @	 public exceptional_behavior
	  @	 requires filename != null && new File(filename).exists();
	  @  signals (Exception e) e instanceof FileNotFoundException;
	  @*/
	@Override
	public void setFile(String filename) throws FileNotFoundException {
		if (filename == null) {
			throw new IllegalArgumentException("Valore nullo");
		}
		this.filename = filename;
		File file = new File(filename);
		if (!file.exists()) {
			throw new FileNotFoundException();
		}
	}

	
	/*@ also ensures \result <==> hasKeyWords() && !hasWrongLines();
	  @*/
	@Override
	public /*@ pure @*/ boolean isWellFormed() throws FileNotFoundException, IOException {
		boolean hasKeys = hasKeyWords();
		boolean hasWrongLines = hasWrongLines();
	    return hasKeys && !hasWrongLines;
	}

	//@ also ensures \result == false ==> (this instanceof McModel ==> a instanceof AnswerMC);
	//@ also ensures \result == false ==> (this instanceof TfModel ==> a instanceof AnswerTF);
	@Override
	public boolean insertAnswer(IAnswers a) throws IOException {
		if ((this instanceof McModel && !(a instanceof AnswerMC))
				|| (this instanceof TfModel && !(a instanceof AnswerTF))) {
			return false;
		}
		FileWriter fw;
		fw = new FileWriter(filename,true);
		fw.write(a.toString() + System.lineSeparator());	//appends the string to the file
	    fw.close();
		return true;
	}

	protected String[] splitLine(String string) {
		if (string == null) {
			return null;
		}
		string = string.substring(1, string.length() - 1);
		//System.out.println(string);
		String[] splitted = string.split("\",\"");
		for (int i=0; i < splitted.length; i++) {
			splitted[i] = splitted[i].replace("\\\"", "\"");
//			System.out.println(splitted[i]);
		}
		return splitted;
	}
	
	@Override
	public /*@ pure @*/ boolean hasWrongLines() throws FileNotFoundException, IOException {
		BufferedReader br = new BufferedReader(new FileReader(new File(filename)));
		//Skip two lines
		br.readLine();
		br.readLine();
		//cycle over file
		String line;
		while ((line = br.readLine()) != null) {
	       String[] words = splitLine(line);
	       if (words.length != FIELDS.length || (!words[6].equals("A") && !words[6].equals("B") 
	    		   && !words[6].equals("D") && !words[6].equals("D"))){
	    	   return true;
	       }
	    }
		return false;
	}
	
	 
	@Override
	public /*@ pure @*/ boolean hasKeyWords() throws FileNotFoundException, IOException {
		BufferedReader br = new BufferedReader(new FileReader(new File(filename)));
		String first_line = br.readLine();
		String second_line = br.readLine();
		br.close();
		boolean fres = first_line != null && first_line.equals(MAGIC_KEY);
		String[] splitted = splitLine(second_line);
		boolean sres = splitted != null && Arrays.equals(splitted, FIELDS);
		return fres && sres;
	}

}
