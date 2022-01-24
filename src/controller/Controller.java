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
import model.Model;
import model.TfModel;

public class Controller implements IController{

	private static final String MORE_INJECTIONS = "I campi contengono uno o più injections (stringa \",\"); la stringa verrà rimossa ";
	private static final String INJECTION_STRING = "\",\"";
	private static final String INSERTED_QUIZ = "Hai inserito il quiz correttamente!";
	private static final String CANNOT_REMOVE_LINES = "Impossibile rimuovere il contenuto sbagliato; Riprovare";
	private static final String JUST_INSERTED_MESSAGE = "Hai appena inserto questo quiz!!";
	private static final String SEARCH_ABORT_MESSAGE = "Search abort";
	private static final String REMOVED_LINES_MESSAGE = "Sono state rimosse le righe sbagliate";
	private static final String WRONG_LINES_MESSAGE = "Attenzione: alcune linee sono scorrette, verranno rimosse";
	private static final String WRONG_FORMAT_MESSAGE = "Attenzione: Il formato del file non è corretto, controllare le magic words. In particolare verificare che le prime due righe del file siano: ";
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
	
	// also requires answers.length == 4 && (\forall int i; 0<= i && i < 4; answers[i] != null);
	// also requires correctAns.equals("A") || correctAns.equals("B") || correctAns.equals("C") || correctAns.equals("D");
	/* also ensures \result <==> ((\forall int i; 0<= i && i < 4; !answers[i].isEmpty()) && !category.isEmpty() && !question.isEmpty() && !correctAns.isEmpty() && !caption.isEmpty() &&
	  	!model_mc.hasKeyWords());
	*/
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
		if (correctAns.isEmpty() || (!correctAns.equals("A") && !correctAns.equals("B") && !correctAns.equals("C") && !correctAns.equals("D"))) {
			throw new IllegalArgumentException("Non hai inserito una delle possibili risposte (A-B-C-D)");
		}
		/*--------------------------------------------------------------*/
		//check empty strings
		if (category.isEmpty() || question.isEmpty() || caption.isEmpty()) {
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
			//some assert
			assert answers != null && answers.length == 4;
			
			//check injection
			if (category.contains(INJECTION_STRING) || question.contains(INJECTION_STRING) || answers[0].contains(INJECTION_STRING) || answers[1].contains(INJECTION_STRING) || 
			answers[2].contains(INJECTION_STRING) || answers[3].contains(INJECTION_STRING) || caption.contains(INJECTION_STRING)) {
				category = category.replace(INJECTION_STRING, "");
				question = question.replace(INJECTION_STRING, "");
				answers[0] = answers[0].replace(INJECTION_STRING, "");
				answers[1] = answers[1].replace(INJECTION_STRING, "");
				answers[2] = answers[2].replace(INJECTION_STRING, "");
				answers[3] = answers[3].replace(INJECTION_STRING, "");
				caption = caption.replace(INJECTION_STRING, "");
				
				view.displayInfoErrorMessages(MORE_INJECTIONS);
			}
			
			//new answer
			IAnswers a = new AnswerMC(0, category, question, answers[0], 
					answers[1], answers[2], answers[3], correctAns, caption);
			
			//check if just inserted
			if (a.equals(lastMc)) {
				view.displayInfoErrorMessages(JUST_INSERTED_MESSAGE);
				return false;
			}
			
			//insert in file
			boolean inserted = true;	
			inserted = model_mc.insertAnswer(a);
			lastMc = a;
			view.displayInfoErrorMessages(INSERTED_QUIZ);
			return inserted;
			
		}catch (FileNotFoundException e) {
			view.displayInfoErrorMessages(FILE_NOT_FOUND_MESSAGE);
			return false;
		}catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
		
	}

	private boolean check_correct_format(IModel model) throws FileNotFoundException, IOException {
		if (!model.hasKeyWords()) {
			view.displayInfoErrorMessages(WRONG_FORMAT_MESSAGE + System.lineSeparator() + model.getFirstLine() + System.lineSeparator() + model.getSecondLine());
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
					view.displayInfoErrorMessages(CANNOT_REMOVE_LINES);
					return false;
				}
			}else {
				return true;
			}
		}
	}
	
	
	@Override
	public boolean onInsertTFButtonPressed(/*@ non_null @*/ String category, /*@ non_null @*/ String question, boolean correctAnserwer, /*@ non_null @*/ String caption){
		if (category == null || question == null || caption == null) {
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
			//check injection
			if (category.contains(INJECTION_STRING) || question.contains(INJECTION_STRING) || caption.contains(INJECTION_STRING)) {
				category = category.replace(INJECTION_STRING, "");
				question = question.replace(INJECTION_STRING, "");
				caption = caption.replace(INJECTION_STRING, "");
				
				view.displayInfoErrorMessages(MORE_INJECTIONS);
			}
			
			IAnswers a = new AnswerTF(0, category, question, correctAnserwer, caption);
			//check if just inserted
			if (a.equals(lastTf)) {
				view.displayInfoErrorMessages(JUST_INSERTED_MESSAGE);
				return false;
			}
			boolean inserted = model_tf.insertAnswer(a);
			lastTf = a;
			view.displayInfoErrorMessages(INSERTED_QUIZ);
			return inserted;
		}catch (FileNotFoundException e) {
			view.displayInfoErrorMessages(FILE_NOT_FOUND_MESSAGE);
			return false;
		}catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
	}

	
	@Override
	public boolean onSearchButtonPressed(String category) {
		//check input
		if (category == null) {
			throw new IllegalArgumentException("Campo non deve essere nullo");
		}
		
		try {
			boolean correctMc = check_correct_format(model_mc);
			boolean correctTf = check_correct_format(model_tf);
			if (!correctMc || !correctTf) {
				view.displayInfoErrorMessages(SEARCH_ABORT_MESSAGE);
				return false;
			}
			IAnswers[] ansMC = model_mc.readAnswers(category);
			IAnswers[] ansTF = model_tf.readAnswers(category);
			
			//check null pointer
			if (ansMC == null && ansTF == null) {
				view.displayQuizMessages(QUIZ_NOT_FOUND_MESSAGE + category);
				return true;
			}
			assert ansMC != null || ansTF != null : "ansMc e ansTF sono ambedue nulli!";
			//calculate lenght of list
			int lenght = 0;
			if (ansMC != null)	lenght += ansMC.length;
			if (ansTF != null)	lenght += ansTF.length;
			//some assert
			assert lenght > 0 : "lenght nulla!";
			// (ansMC != null && ansTF != null) --> lenght = ansMC.length + ansTF.length;
			assert !(ansMC != null && ansTF != null) || (lenght == ansMC.length + ansTF.length);
			// ansMC != null && ansTF == null --> lenght == ansMC.length;
			// ansTF != null && ansMC == null --> lenght == ansTF.length;
			assert !(ansMC != null && ansTF == null) || lenght == ansMC.length;
			assert !(ansTF != null && ansMC == null) || lenght == ansTF.length;
			
			//fill final array
			IAnswers[] allAns = new IAnswers[lenght];
			//first, fill witch ansMC
			if (ansMC != null) {
				for (int i=0; i < ansMC.length; i++) {
					allAns[i] = ansMC[i];
				}
			}
			//second fill with ansTF
			if (ansTF != null) {
				int delta = 0;
				if (ansMC != null) {
					delta = ansMC.length;
				}
				for (int i=0; i < ansTF.length; i++) {
					allAns[i + delta] = ansTF[i];
				}
			}
//			//concat array
//			List<IAnswers> resultList = new ArrayList<>(lenght);
//		    if (ansMC != null) 		Collections.addAll(resultList, ansMC);
//		    if (ansTF != null) 		Collections.addAll(resultList, ansTF);
//		    @SuppressWarnings("unchecked")
//		    //the type cast is safe as the array1 has the type T[]
//		    IAnswers[] resultArray = (IAnswers[]) Array.newInstance(ansMC.getClass().getComponentType(), 0);
//		    IAnswers[] ans = resultList.toArray(resultArray);
//			//create message
			assert allAns != null && allAns.length > 0;
		    String message = "";
		    for (IAnswers ans : allAns) {
				message += ans.toStringWithLine() + System.lineSeparator();
			}
		    //assert striga non vuota
		    assert !message.isEmpty() : "Messaggio vuoto";
		    view.displayQuizMessages(message);
		    return true;
		}catch (FileNotFoundException e) {
			view.displayInfoErrorMessages(FILE_NOT_FOUND_MESSAGE);
			return false;
		}catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
		
	}

	
	@Override
	public boolean onChangeMCFilePath(String filename) {
		//input check
		if (filename == null)	throw new IllegalArgumentException("Stringa nulla in ingresso");
		try {
			model_mc.setFile(filename);
			boolean correct = check_correct_format(model_mc);
			if (correct) {
				view.displayInfoErrorMessages(CHANGED_FILE_MESSAGE + filename);
			}
			return correct;
		} catch (FileNotFoundException e) {
			view.displayInfoErrorMessages(FILE_NOT_FOUND_MESSAGE + filename);
			return false;
		} catch (IOException e) {
			view.displayInfoErrorMessages(GENERAL_ERROR_MESSAGE);
			return false;
		}
	}

	
	@Override
	public boolean onChangeTFFilePath(String filename) {
		//input check
		if (filename == null)	throw new IllegalArgumentException("Stringa nulla in ingresso");
		try {
			model_tf.setFile(filename);
			boolean correct = check_correct_format(model_tf);
			if (correct) {
				view.displayInfoErrorMessages(CHANGED_FILE_MESSAGE + filename);
			}
			return correct;
		} catch (FileNotFoundException e) {
			view.displayInfoErrorMessages(FILE_NOT_FOUND_MESSAGE + filename);
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
	public static String getJustInsertedMessage() {
		return JUST_INSERTED_MESSAGE;
	}
	
	public static String getSearchAbortMessage() {
		return SEARCH_ABORT_MESSAGE;
	}

	public static String getInsertedQuiz() {
		return INSERTED_QUIZ;
	}

	public static String getCannotRemoveLines() {
		return CANNOT_REMOVE_LINES;
	}
	
	public static String getMoreInjectionString() {
		return MORE_INJECTIONS;
	}
	
	
	/*********/
}
