package model;
import java.util.regex.*;

public interface IAnswers {
	//Quote e dash-quote constants
	public static final String QUOTE = "\"";
	public static final String DASHQUOTE = "\\\"";
	public static final String WIN_LINE_SEPARATOR = "\\r\\n";
	
	/**
	 * ONLY FOR TESTING
	 * @return
	 */
	public String getCategory();
	/**
	 * ONLY FOR TESTING
	 * @return
	 */
	public String getQuestion();
	/**
	 * ONLY FOR TESTING
	 * @return
	 */
	public String getCaption();
	/**
	 * Ritorna il quiz sottoforma di stringa. Stampa la linea in cui si trova il quiz nel file.
	 * Stampa al posto del DASHQUOTE il semplice QUOTE.
	 * @return stringa non vuota
	 */
	//@ requires true;
	//@ ensures \result != null && !\result.isEmpty();
	//@ ensures Pattern.matches(, \result);
	public String toStringWithLine();
	
	/**
	 * Ritorna il quiz sotto forma di stringa. Stampa il contenuto che servirà per scrivere nel file.
	 * Stampa al posto del QUOTE il DASHQUOTE e il line separator In WIN_LINE_SEPARATOR
	 * @return stringa non vuota
	 */
	//@ requires true;
	//@ ensures \result != null && !\result.isEmpty();
	//@ ensures Pattern.matches(QUOTE + "[^" + QUOTE + System.lineSeparator() + "]+" + "(\",\"[^" + QUOTE + System.lineSeparator() + "])+" + QUOTE, \result);
	public String toStringToFile();
}