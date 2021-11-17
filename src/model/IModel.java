package model;

import java.io.FileNotFoundException;
import java.io.IOException;

public interface IModel {
	
	/**
	 * Setta il file corrente
	 * @param filename percorso del file
	 * @throws FileNotFoundException se non trova il file 
	 */
	public void setFile(String filename) throws FileNotFoundException;
	/**
	 * Controlla che il file ha le parole chiave nell'intestazione. In particolare :
	 * <ul>
	 * 	<li> per Multiple-Choice
	 * 	<ol>
	 * 	 <li> "MC"
	 * 	 <li> "category","question","A","B","C","D","answer","caption"
	 *  </ol>
	 *  <li> per True-False
	 * 	<ol>
	 * 	 <li> "TF"
	 * 	 <li> "category","question","answer","caption"
	 *  </ol>
	 * </ul>
	 * @return true se ha l'intestazione come sopra definito, false altrimenti (strighe diverse o nessuna riga o meno di due)
	 * @throws FileNotFoundException se non trova il file
	 * @throws IOException per problemi di I/O
	 */
	public boolean hasKeyWords() throws FileNotFoundException, IOException;
	/**
	 * Controlla se nel file sono inserite le righe corrette (viene considerato corretto anche se non ci sono righe 
	 * -tralasciando le prime duerighe di intestazione-). In particolare :
	 * <ul>
	 * 	<li> MC : "categoria","domanda","risposta A","risposta B","risposta C","risposta D","A"|"B"|"C"|"D","didascalia";
	 *  <li> TF : "categoria","domanda",true|false,"didascalia";
	 * </ul>
	 * @return true se ha qualche linea errata, false altrimenti (anche se senza linee)
	 * @throws FileNotFoundException se non trova il file
	 * @throws IOException problemi I/O
	 */
	public boolean hasWrongLines() throws FileNotFoundException, IOException;
	/**
	 * Controlla che il linguaggio del file sia ben formato, ovvero abbia le righe ({@link #hasWrongLines() hasWrongLines}) 
	 * e l'intestazione coretta ({@link #hasKeyWords() hasKeyWords})
	 * @return true se ben formato, ovvero {@link #hasWrongLines() hasWrongLines} è false e {@link #hasKeyWords() hasKeyWords} è true, false altrimenti
	 * @throws FileNotFoundException Eccezione lanciata se non trova il file
	 * @throws IOException Eccezione Generica di errore di sI/O
	 */
	public boolean isWellFormed() throws FileNotFoundException, IOException;
	/**
	 * Inserisci il quiz nel file corrente. <br/>
	 * Attenzione : per inserire il quiz, se l'oggetto che invoca il metodo è di tipo {@link McModel McModel}, 
	 * allora il parametro passato deve essere di tipo {@link AnswerMC AnswerMC},
	 * altrimenti se è di tipo {@link TfModel TfModel} allora il parametro è di tipo {@link AnswerTF AnswerTF}. <br/>
	 * Se viene invocato in modo scorretto, allora ritorna false e non inserisce il quiz.
	 * @param a quiz da inserire (di tipo {@link AnswerMC AnswerMC} o {@link AnswerTF AnswerTF})
	 * @return true se inserisci in modo corretto, false altrimenti (vedi sopra).
	 * @throws IOException 
	 */
	public boolean insertAnswer(IAnswers a) throws IOException;
	/**
	 * Legge il file (MC o TF) e ritorna la lista di quiz che corrispondono alla stringa di ricerca. 
	 * Per la lettura è necessario che il file sia ben formato {@link #isWellFormed() isWellFormed}, altrimenti lancia IllegalArgumentException.
	 * @param category Stringa di ricerca della categoria (se vuota ricerca tutto, altrimenti solo la categoria specificata); 
	 * se null lancia IllegalArgumentException
	 * @return Ritorna array di IAnswers corrispondenti alla stringa di ricerca, null se non trova quiz corrispndenti alla stringa 
	 * o se file non contiene alcun quiz.
	 * @throws FileNotFoundException se il file (MC o TF) non esiste
	 * @throws IOException Errore di I/O generale
	 */
	public IAnswers[] readAnswers(String category) throws FileNotFoundException, IOException;
	/**
	 * Rimuove le righe che non seguono il formato del file, ovvero se possiede l'intestazione corretta (vedi {@link #hasKeyWords() hasKeyWords} ritorna vero), 
	 * ma possiede righe non del formato corretto (vedi {@link #hasWrongLines() hasWrongLines} ritorna vero), altrimenti lancia IllegalArgumentException.
	 * @return true se rimosse, false altrimenti
	 * @throws IOException problemi generali I/O
	 */
	public boolean removeWrongLines() throws FileNotFoundException, IOException;
	/**
	 * 
	 * @return
	 */
	public String getFirstLine();
	public String getSecondLine();
	
}
