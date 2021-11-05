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
	 * Controlla che il file ha le parole chiave
	 * @return true se ha tutte le parole chiave, false altrimenti
	 * @throws FileNotFoundException se non trova il file
	 * @throws IOException per problemi di I/O
	 */
	public boolean hasKeyWords() throws FileNotFoundException, IOException;
	/**
	 * Controlla se nel file sono inserite le righe corrette
	 * @return true se ha qualche linea errata, false altrimenti
	 * @throws FileNotFoundException se non trova il file
	 * @throws IOException problemi I/O
	 */
	public boolean hasWrongLines() throws FileNotFoundException, IOException;
	/**
	 * Controlla che il linguaggio del file sia ben formato (vedere ogni singolo formato)
	 * @return true se ben formato, false altrimenti
	 * @throws FileNotFoundException Eccezione lanciata se non trova il file
	 * @throws IOException Eccezione lanciata se non trova il file
	 */
	public boolean isWellFormed() throws FileNotFoundException, IOException;
	/**
	 * Inserisci il quiz nel file corrente
	 * @param a quiz da inserire
	 * @return true se inserisci, false se IAnswer è quello corretto.
	 * @throws IOException 
	 */
	public boolean insertAnswer(IAnswers a) throws IOException;
	/**
	 * 
	 * @param category Stringa di ricerca della categoria (se vuota ricerca tutto, altrimenti solo la categoria specificata)
	 * @return Ritorna la lista di quiz IAnswers trovate, null se non trova nulla.
	 * @throws FileNotFoundException se il file non esiste
	 * @throws IOException
	 */
	public IAnswers[] readAnswers(String category) throws FileNotFoundException, IOException;
	/**
	 * Rimuove le righe che non seguono il formato 
	 * @return true se rimosse, false altrimenti
	 * @throws IOException problemi generali I/O
	 */
	public boolean removeWrongLines() throws FileNotFoundException, IOException;
}
