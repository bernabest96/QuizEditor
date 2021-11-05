package controller;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.List;
import java.util.Collections;

import view.IView;
import view.View;
import model.AnswerMC;
import model.AnswerTF;
import model.IAnswers;
import model.IMCAnswers;
import model.IModel;
import model.McModel;
import model.TfModel;

public class Controller implements IController{

	private static final String JUST_INSERTED_MESSAGE = "Hai appena inserto questo quiz!!";
	private static final String NO_FOUND_MESSAGE = "Nessun risultato trovato";
	private static final String SEARCH_ABORT_MESSAGE = "Search abort";
	private static final String REMOVED_LINES_MESSAGE = "Sono state rimosse le righe sbagliate";
	private static final String WRONG_LINES_MESSAGE = "Attenzione: alcune linee sono scorrette, verranno rimosse";
	private static final String WRONG_FORMAT_MESSAGE = "Attenzione: Il formato del file non è corretto, controllare le magic words";
	private static final String PARAMETER_EMPTY_02 = "Almeno un parametro delle risposte è vuoto; Riempi tutti i campi";
	private static final String PARAMETER_EMPTY_01 = "Hai inserito alcuni parametri vuoti; Riempi tutti i campi";
	private static final String CHANGED_FILE_MESSAGE = "è stato cambiato il file con successo ora il file è ";
	private static final String FILE_NOT_FOUND_MESSAGE = "Il file non esiste: ";
	private static final String QUIZ_NOT_FOUND_MESSAGE = "Non sono state trovati quiz con questa stringa di ricerca: ";
	private /*@ spec_public @*/ /*@ non_null @*/ McModel model_mc;
	private /*@ spec_public @*/ /*@ non_null @*/ TfModel model_tf;
	private /*@ spec_public @*/ /*@ non_null @*/ IView view;

	private static final String GENERAL_ERROR_MESSAGE = "Problemi nella lettura/scrittura del file\n";
	private IAnswers lastMc, lastTf;
	
	public Controller(/*@ non_null @*/ McModel  model_mc, /*@ non_null @*/ TfModel model_tf, /*@ non_null @*/ IView view) throws Exception {
		if (model_mc == null || model_tf == null || view == null) {
			throw new IllegalArgumentException("Non hai inizializzato o i modelli o la view");
		}
		assert model_mc != null;
		assert model_tf != null;
		assert view != null;
		
		this.model_mc = model_mc;
		this.model_tf = model_tf;
		this.view = view;
		
		lastMc = null;
		lastTf = null;
	}
	
	//@ also requires answers.length == 4 && (\forall int i; 0<= i && i < 4; answers[i] != null);
	//@ also requires correctAns.equals("A") || correctAns.equals("B") || correctAns.equals("C") || correctAns.equals("D");
	/*@ also ensures \result <==> ((\forall int i; 0<= i && i < 4; !answers[i].isEmpty()) && !category.isEmpty() && !question.isEmpty() && !correctAns.isEmpty() && !caption.isEmpty() &&
	  @	!model_mc.hasKeyWords());
	@*/
	@Override
	public boolean onInsertMCButtonPressed(/*@ non_null @*/ String category, /*@ non_null @*/ String question, 
			/*@ non_null @*/ String[] answers, /*@ non_null @*/ String correctAns, /*@ non_null @*/ String caption) {
		/*---------------------all input checks------------------------*/
		//check null pointers
		if (category == null || question == null || answers == null || correctAns == null || caption == null) {
			throw new IllegalArgumentException("Hai inserito alcuni valori nulli");
		}
		for (String ans : answers) {
			if (ans == null) {
				throw new IllegalArgumentException("Hai inserito alcuni valori nulli");
			}
		}
		if (answers.length != 4) {
			throw new IllegalArgumentException("La dimensione dell'input non è 4");
		}
		if (!correctAns.equals("A") && correctAns.equals("B") && correctAns.equals("C") && correctAns.equals("D")) {
			throw new IllegalArgumentException("Non hai inserito una delle possibili risposte (A-B-C-D)");
		}
		/*--------------------------------------------------------------*/
		//check empty strings
		if (category.isEmpty() || question.isEmpty() || correctAns.isEmpty() || caption.isEmpty()) {
			view.displayInfoErrorMessages(PARAMETER_EMPTY_01);
			return false;
		}
		boolean isEmpty = false;
		for (String a : answers) {
			assert a != null;
			isEmpty = isEmpty || a.isEmpty();
		}
		if (isEmpty) {
			view.displayInfoErrorMessages(PARAMETER_EMPTY_02);
			return false;
		}
		//check correct format
		try {
			//passiamo il parametro e controlliamo il tipo ritornato
			boolean correct = check_correct_format(model_mc);
			if (!correct) {
				return false;
			}
		} catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
		
		//insert
		IAnswers a = new AnswerMC(category, question, answers[0], answers[1], 
				answers[2], answers[3], correctAns, caption);
		if (a.equals(lastMc)) {
			view.displayInfoErrorMessages(JUST_INSERTED_MESSAGE);
		}
		boolean inserted = true;
		try {
			inserted = model_mc.insertAnswer(a);
			lastMc = a;
			view.displayInfoErrorMessages("Hai inserito il quiz correttamente!");
		} catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
		
		return inserted;
	}

	private boolean check_correct_format(IModel model) throws FileNotFoundException, IOException {
		if (!model.hasKeyWords()) {
			view.displayInfoErrorMessages(WRONG_FORMAT_MESSAGE);
			return false;
		}else {
			assert model.hasKeyWords();
			if (model.hasWrongLines()) {
				view.displayInfoErrorMessages(WRONG_LINES_MESSAGE);
				boolean removed = model.removeWrongLines();
				if (removed) {
					view.displayInfoErrorMessages(REMOVED_LINES_MESSAGE);
					return true;
				}else {
					view.displayInfoErrorMessages("Impossibile rimuovere il contenuto sbagliato; Riprovare");
					return false;
				}
			}else {
				return true;
			}
		}
	}
	
	
	@Override
	public boolean onInsertTFButtonPressed(/*@ non_null @*/ String category, /*@ non_null @*/ String question, boolean correctAnserwer, /*@ non_null @*/ String caption){
		if (category == null && question == null && caption == null) {
			throw new IllegalArgumentException("Alcuni input sono nulli");
		}
		//campi vuoti
		if (category.isEmpty() || question.isEmpty() || caption.isEmpty()) {
			view.displayInfoErrorMessages(PARAMETER_EMPTY_01);
			return false;
		}
		try {
			boolean correct = check_correct_format(model_tf);
			if (!correct) {
				return false;
			}
		}catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
		IAnswers a = new AnswerTF(category, question, correctAnserwer, caption);
		if (a.equals(lastTf)) {
			view.displayInfoErrorMessages(JUST_INSERTED_MESSAGE);
		}
		boolean inserted;
		try {
			inserted = model_tf.insertAnswer(a);
			lastTf = a;
		} catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
		return inserted;
	}

	public static String getJustInsertedMessage() {
		return JUST_INSERTED_MESSAGE;
	}

	@Override
	public boolean onSearchButtonPressed(String category) {
		
		if (category == null) {
			throw new IllegalArgumentException("Campo non deve essere nullo");
		}
		//Alcuni assert
		assert category != null;
		try {
			assert model_mc.isWellFormed() && model_tf.isWellFormed();
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
			assert false;
		} catch (IOException e1) {
			e1.printStackTrace();
			assert false;
		}
		//fine assert
		try {
			boolean correctMc = check_correct_format(model_mc);
			boolean correctTf = check_correct_format(model_tf);
			if (!correctMc || !correctTf) {
				view.displayInfoErrorMessages(SEARCH_ABORT_MESSAGE);
				return false;
			}
			IAnswers[] ansMC = model_mc.readAnswers(category);
			IAnswers[] ansTF = model_tf.readAnswers(category);
			//concat array
			List<IAnswers> resultList = new ArrayList<>(ansMC.length + ansTF.length);
		    Collections.addAll(resultList, ansMC);
		    Collections.addAll(resultList, ansTF);
		    @SuppressWarnings("unchecked")
		    //the type cast is safe as the array1 has the type T[]
		    IAnswers[] resultArray = (IAnswers[]) Array.newInstance(ansMC.getClass().getComponentType(), 0);
		    IAnswers[] ans = resultList.toArray(resultArray);
			//create message
		    String message = "";
		    for (IAnswers a : ans) {
				message += a.toString() + System.lineSeparator();
			}
		    if (message.isEmpty()) {
		    	view.displayInfoErrorMessages(NO_FOUND_MESSAGE);
		    }else {
		    	view.displayQuizMessages(message);
		    }
		    return true;
		}catch (FileNotFoundException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
		
	}

	
	public static String getNoFoundMessage() {
		return NO_FOUND_MESSAGE;
	}

	public static String getSearchAbortMessage() {
		return SEARCH_ABORT_MESSAGE;
	}

	public static String getWrongFormatMessage() {
		return WRONG_FORMAT_MESSAGE;
	}

	@Override
	public boolean onChangeMCFilePath(String filename) {
		try {
			model_mc.setFile(filename);
			boolean correct = check_correct_format(model_mc);
			if (correct) {
				view.displayInfoErrorMessages(CHANGED_FILE_MESSAGE + filename);
			}
			return correct;
		} catch (FileNotFoundException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		} catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
		
	}

	
	@Override
	public boolean onChangeTFFilePath(String filename) {
		try {
			model_tf.setFile(filename);
			boolean correct = check_correct_format(model_tf);
			if (correct) {
				view.displayInfoErrorMessages(CHANGED_FILE_MESSAGE + filename);
			}
			return correct;
		} catch (FileNotFoundException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		} catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
	}

	/**** ONLY FOR TESTING ****/
	
	public static String getRemovedLinesMessage() {
		return REMOVED_LINES_MESSAGE;
	}

	public static String getWrongLinesMessage() {
		return WRONG_LINES_MESSAGE;
	}

	public static String getNotCorrectFileMessage() {
		return WRONG_FORMAT_MESSAGE;
	}

	public static String getParameterEmpty02() {
		return PARAMETER_EMPTY_02;
	}

	public static String getParameterEmpty01() {
		return PARAMETER_EMPTY_01;
	}

	public static String getChangedFileMessage() {
		return CHANGED_FILE_MESSAGE;
	}

	public static String getGeneralErrorMessage() {
		return GENERAL_ERROR_MESSAGE;
	}
	public static String getFileNotFoundMessage() {
		return FILE_NOT_FOUND_MESSAGE;
	}
	public static String getQuizNotFoundMessage() {
		return QUIZ_NOT_FOUND_MESSAGE;
	}
}
