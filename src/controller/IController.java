package controller;

public interface IController {
	/**
	 * Il metodo <b> onInsertMCButtonPressed </b> viene invocato quando nella View viene inserita un nuovo quiz di tipo Multiple
	 * Choice (MC) premendo il pulsante corripondente. Prende in input le risposte e verifica :
	 * <ul>
	 * 	<li> le stringhe siano non nulle (altrimenti lancia ArgumentException) </li>
	 * 	<li> le stringhe siano vuote (stampa un messaggio di errore sulla console)
	 *  <li> le stringhe non contengano caratteri del tipo "," (virole comprese) che verranno rimosse.
	 *  <li> il file del Model sia ben formato
	 *  <li> contiene righe scorrette, che verranno eliminate
	 * </ul>
	 * Se si presenta uno di questi errori, viene invocata la View con un messaggio di errore. Se non si presenta nessuno dei problemi sopra citati, 
	 * allora il quiz viene inserito nel file e se si verificano generali problemi di I/O viene stampato un messaggio di errore.
	 * @param category stringa che rappresenta la categoria (non null)
	 * @param question stringa che rappresenta la domanda
	 * @param answers array di stringhe che rappresenta le risposte (4 risposte)
	 * @param correctAns stringa che rappresenta la risposta giusta ("A", "B", "C" o "D")
	 * @param caption stringa che rappresenta la didascalia
	 * @return true se inserisce senza problemi il quiz, false in tutti gli altri casi sopra descritti.
	 */
	public boolean onInsertMCButtonPressed(String category, String question, String[] answers, String correctAns, String caption);
	/**
	 * 
	 * @param category
	 * @param question
	 * @param correctAnserwer
	 * @param caption
	 * @return
	 */
	public boolean onInsertTFButtonPressed(String category, String question, boolean correctAnserwer, String caption);
	public boolean onSearchButtonPressed(String category);
	public boolean onChangeMCFilePath(String filename);
	public boolean onChangeTFFilePath(String filename);
}
