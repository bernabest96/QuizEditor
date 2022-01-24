package fsm;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Map;
import java.util.Random;

import org.junit.Assert;

import edu.uci.ics.jung.graph.util.Pair;
import model.AnswerMC;
import model.IAnswers;
import model.McModel;
import model.Model;
import model.TfModel;
import nz.ac.waikato.modeljunit.Action;
import nz.ac.waikato.modeljunit.FsmModel;
import nz.ac.waikato.modeljunit.GraphListener;
import nz.ac.waikato.modeljunit.GreedyTester;
import nz.ac.waikato.modeljunit.ModelTestCase;
import nz.ac.waikato.modeljunit.Tester;
import nz.ac.waikato.modeljunit.VerboseListener;
import nz.ac.waikato.modeljunit.coverage.CoverageMetric;
import nz.ac.waikato.modeljunit.coverage.StateCoverage;
import nz.ac.waikato.modeljunit.coverage.TransitionCoverage;

public class EditorFSM implements FsmModel{
	//Costanti
	private static final String FILEPATH_MC_01 = "./test/fsm/test_mc.txt";
	private static final String FILEPATH_MC_NOT_EXISTS = "test_not_exist_file.txt";
	private static final String FILEPATH_NOT_CORRECT = "./test/fsm/test_not_correct_mc.txt";
	private static int MAX_SIZE = 3;
	
	//EFSM states
	enum Category {CATEGORY_1, CATEGORY_2, CATEGORY_3};
//	enum Quiz {QUESTION01, QUESTION02, QUESTION03}
	enum State {CHOOSE_FILE, CHOOSEN_RIGHT, CHOOSEN_NOT_EXIST, CHOSEN_WRONG_FILE, INSERTED, PRINT_C_1, PRINT_C_2, PRINT_C_3, PRINT_C_ALL, WRONG_USER_INSERT}
	State state;
	ArrayList<Category> file;
	
	//SUT
	Model mc;
	Model tf;
	
	/******* AZIONI FSM *****/
	public EditorFSM(){
		state = State.CHOOSE_FILE;
		file = new ArrayList<EditorFSM.Category>();
		//sut
		try {
			mc = new McModel(FILEPATH_MC_01);
			resetFile();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	private void resetFile() throws IOException {
		BufferedWriter bw = new BufferedWriter(new FileWriter(new File(FILEPATH_MC_01)));
		bw.write("\"MC\"");
		bw.newLine();
		bw.write("\"category\",\"question\",\"A\",\"B\",\"C\",\"D\",\"answer\",\"caption\"");
		bw.newLine();
		bw.close();
	}
	
	private void insertSomeErrors(String errorString) throws IOException {
		BufferedWriter bw = new BufferedWriter(new FileWriter(new File(FILEPATH_MC_01)));
		bw.write(errorString);
		bw.close();
	}
	
	@Action
	public void SetFile() throws FileNotFoundException {
		state = State.CHOOSEN_RIGHT;
		assert file.isEmpty() : "In questo stato la lista deve essere vuoto";
		//sut
		mc.setFile(FILEPATH_MC_01);
	}
	
	public boolean SetFileGuard() {
		return state.equals(State.CHOOSE_FILE);
	}
	
	@Action
	public void SetFileNotCorrect() throws IOException {
		state = State.CHOSEN_WRONG_FILE;
		//sut
		mc.setFile(FILEPATH_NOT_CORRECT);
		assertFalse(mc.hasKeyWords());
	}
	
	public boolean SetFileNotCorrectGuard() {
		return state.equals(State.CHOOSE_FILE);
	}
	
	@Action
	public void SetFileNotExists() {
		state = State.CHOOSEN_NOT_EXIST;
		Assert.assertThrows(FileNotFoundException.class, () -> {
			mc.setFile(FILEPATH_MC_NOT_EXISTS);
		});
	}
	
	public boolean SetFileNotExistsGuard() {
		return state.equals(State.CHOOSE_FILE);
	}
	
	@Action
	public void backToChooseFile() {
		reset(true);
	}
	
	public boolean backToChooseFileGuard() {
		return state.equals(State.CHOSEN_WRONG_FILE) || state.equals(State.CHOOSEN_NOT_EXIST);
	}
	
	private boolean notChooseState() {
		return  !state.equals(State.CHOOSE_FILE) && 
				!state.equals(State.CHOSEN_WRONG_FILE) && 
				!state.equals(State.CHOOSEN_NOT_EXIST);
	}
	
	
	
	@Action
	public void insertC1() throws IOException {
		state = State.INSERTED;
		if (file.size() < MAX_SIZE) {
			file.add(Category.CATEGORY_1);
			//sut
			IAnswers a = new AnswerMC(0, Category.CATEGORY_1.toString(), "question", "A", "B", "C", "D", "A", "caption");
			Assert.assertTrue( mc.insertAnswer(a));
			//read last line in file
			
		}else {
			assert file.size() == MAX_SIZE;
			state = State.CHOOSEN_RIGHT;
			file.clear();
			//sut
			resetFile();
		}
	}
	
	public boolean insertC1Guard() {
		return notChooseState();
	}
	
	@Action
	public void insertC2() throws IOException {
		state = State.INSERTED;
		if (file.size() < MAX_SIZE) {
			file.add(Category.CATEGORY_2);
		}else {
			assert file.size() == MAX_SIZE;
			state = State.CHOOSEN_RIGHT;
			file.clear();
			resetFile();
		}
	}
	
	public boolean insertC2Guard() {
		return notChooseState();
	}
	
	@Action
	public void insertC3() throws IOException {
		state = State.INSERTED;
		if (file.size() < MAX_SIZE) {
			file.add(Category.CATEGORY_3);
		}else {
			assert file.size() == MAX_SIZE;
			state = State.CHOOSEN_RIGHT;
			file.clear();
			resetFile();
//			fail("Not impl yet");
		}
	}
	
	public boolean insertC3Guard() {
		return notChooseState();
	}
 
	/**Read all states**/
	private int searchCateg(Category categ) {
		int num = 0;
		for (Category c : file) {
			if (c.equals(categ)) {
				num++;
			}
		}
		return num;
	}
	
	@Action
	public void printCateg1() throws FileNotFoundException, IOException {
		state = State.PRINT_C_1;
		//sut
		int num = searchCateg(Category.CATEGORY_1);
		IAnswers[] listAns = mc.readAnswers(Category.CATEGORY_1.toString());
		if (num == 0) {
			Assert.assertNull(listAns);
		}else {
			Assert.assertTrue(num > 0 && listAns != null && num == listAns.length);
			for (IAnswers a : listAns) {
				Assert.assertTrue(a instanceof AnswerMC);
				AnswerMC ans = (AnswerMC) a;
				AnswerMC exp = new AnswerMC(0, Category.CATEGORY_1.toString(), "question", "A", "B", "C", "D", "A", "caption");
				Assert.assertEquals(exp, ans);
			}
		}
	}
	
	public boolean printCateg1Guard() {
		return state.equals(State.INSERTED);
	}
	
	@Action
	public void printCateg2() throws FileNotFoundException, IOException {
		state = State.PRINT_C_2;
		//sut
		int num = searchCateg(Category.CATEGORY_2);
		IAnswers[] listAns = mc.readAnswers(Category.CATEGORY_2.toString());
		if (num == 0) {
			Assert.assertNull(listAns);
		}else {
			Assert.assertTrue(num > 0 && listAns != null && num == listAns.length);
			for (IAnswers a : listAns) {
				Assert.assertTrue(a instanceof AnswerMC);
				AnswerMC ans = (AnswerMC) a;
				AnswerMC exp = new AnswerMC(0, Category.CATEGORY_2.toString(), "question", "A", "B", "C", "D", "A", "caption");
				Assert.assertEquals(exp, ans);
			}
		}
		
	}
	
	public boolean printCateg2Guard() {
		return state.equals(State.INSERTED);
	}
	
	@Action
	public void printCateg3() throws FileNotFoundException, IOException {
		state = State.PRINT_C_3;
		//sut
		int num = searchCateg(Category.CATEGORY_3);
		IAnswers[] listAns = mc.readAnswers(Category.CATEGORY_3.toString());
		if (num == 0) {
			Assert.assertNull("il risultato ritornato deve essere nullo", listAns);
		}else {
			Assert.assertTrue(num > 0 && listAns != null && num == listAns.length);
			for (IAnswers a : listAns) {
				Assert.assertTrue(a instanceof AnswerMC);
				AnswerMC ans = (AnswerMC) a;
				AnswerMC exp = new AnswerMC(0, Category.CATEGORY_3.toString(), "question", "A", "B", "C", "D", "A", "caption");
				Assert.assertEquals(exp, ans);
			}
		}
	}
	
	public boolean printCateg3Guard() {
		return state.equals(State.INSERTED);
	}
	
	@Action
	public void printCategAll() throws FileNotFoundException, IOException {
		state = State.PRINT_C_ALL;
		//sut
		IAnswers[] listAns = mc.readAnswers("");
		if (file.size() == 0) {
			Assert.assertNull("il risultato ritornato deve essere nullo", listAns);
			System.out.println(listAns);
		}else {
			Assert.assertTrue(file.size() > 0);
			Assert.assertNotNull("il risultato ritornato NON deve essere nullo", listAns);
			Assert.assertTrue(listAns.length == file.size());
			for (int i=0; i<listAns.length; i++) {
				assertTrue(listAns[i] instanceof AnswerMC);
				AnswerMC act = (AnswerMC) listAns[i];
				AnswerMC exp = new AnswerMC(0, file.get(i).toString(), "question", "A", "B", "C", "D", "A", "caption");
				assertEquals(exp, act);
			}
		}
	}
	
	public boolean printCategAllGuard() {
		return state.equals(State.INSERTED);
	}
	
	/************* user input error *************/
	
//	public void insertUserErrorInFile() throws IOException {
//		state = State.WRONG_USER_INSERT;
//		//sut
//		insertSomeErrors("djaskljdlska" + System.lineSeparator());
//	}
//	
//	public boolean insertUserErrorInFileGuard() {
//		return !state.equals(State.CHOOSE_FILE) && !state.equals(State.PRINT_C_1) &&
//				!state.equals(State.PRINT_C_2) && !state.equals(State.PRINT_C_3) &&
//				!state.equals(State.PRINT_C_ALL);
//	}
	
	public Object getState() {
		String stateToString = state.toString();
		if (state.equals(State.INSERTED) || state.equals(State.CHOOSEN_RIGHT)) {
			stateToString += "; " + file.toString() + "; size: " + file.size();  
		}
		return stateToString;
	}

	@Override
	public void reset(boolean arg0) {
		state = State.CHOOSE_FILE;
		file.clear();
		//sut
		try {
			resetFile();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static void main(String[] args) {
		Tester tester = new GreedyTester(new EditorFSM());
		GraphListener graph = tester.buildGraph();
		CoverageMetric stateCoverage = new StateCoverage();
		tester.addCoverageMetric(stateCoverage);
		CoverageMetric trCoverage = new TransitionCoverage();
		tester.addCoverageMetric(trCoverage);
		tester.addListener(new VerboseListener());
		tester.generate(5000);
		tester.getModel().printMessage(stateCoverage.getName() + " was "+ stateCoverage.toString());
		tester.getModel().printMessage(trCoverage.getName() + " was "+ trCoverage.toString());	
	}

}
