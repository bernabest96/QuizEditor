package junit.model;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Collection;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import model.AnswerMC;
import model.AnswerTF;
import model.IAnswers;
import model.McModel;
import model.Model;

/**
 * Bisogna aver testato prima AnswerMC
 * @author berna
 *
 */
public class McModelTest {
	
	private static final String FILEPATH_CORRECT = "./test/junit/model/correct_mc.txt";
	private static final String FILE_NOT_EXISTS = "boh.txt";
	private static final String FILEPATH_NOT_CORRECT = "./test/junit/model/not_correct_mc.txt";
	private final String CORRECT_KEYS;
	
//	private BufferedReader br = null;
//	private BufferedWriter bw = null;
	private McModel m;
	
	public McModelTest() {
		CORRECT_KEYS = "\"MC\"" + System.lineSeparator() + "\"category\",\"question\",\"A\",\"B\",\"C\",\"D\",\"answer\",\"caption\"" + System.lineSeparator();
	}
	
	@Before
	public void init() throws IOException {
//		br = new BufferedReader(
//				new FileReader(new File(FILEPATH_CORRECT)));
		BufferedWriter bw = new BufferedWriter(new FileWriter(FILEPATH_CORRECT));
		bw.write(CORRECT_KEYS);
		bw.close();
		m = new McModel(FILEPATH_CORRECT);
	}
	
//	@After
//	public void finish() throws IOException {
//		if (br != null)
//        {
//			//ripristina al file di default
//            br.close();
//        }
//		if (bw != null) {
//			bw.close();
//		}
//        br = null;
//        bw = null;
//	}
	
	@Test(expected = IllegalArgumentException.class)
	public void constructor01() throws FileNotFoundException{
		McModel m = new McModel(null);
	}
	
	@Test(expected = FileNotFoundException.class)
	public void constructor02() throws FileNotFoundException{
		McModel m = new McModel(FILE_NOT_EXISTS);
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void setFile01() throws FileNotFoundException {
		m.setFile(null);
	}
	
	@Test(expected = FileNotFoundException.class)
	public void setFile02() throws FileNotFoundException {
		m.setFile(FILE_NOT_EXISTS);
	}
	
	@Test
	public void setFile03() throws FileNotFoundException {
		m.setFile(FILEPATH_NOT_CORRECT);
		m.setFile(FILEPATH_CORRECT);
		//m.setFile non lancia alcuna eccezione
		assertTrue(true);
	}
	
	@Test
	public void hasKey01() throws FileNotFoundException, IOException {
		McModel m = new McModel(FILEPATH_NOT_CORRECT);
		//non ha le parole chiave
		assertFalse(m.hasKeyWords());
	}
	
	@Test
	public void hasKey02() throws FileNotFoundException, IOException {
		//ha le parole chiave
		assertTrue(m.hasKeyWords());
	}
	
	@Test
	public void insert01() throws IOException {
		AnswerMC[] ans = new AnswerMC[4];
		ans[0] = new AnswerMC("category_a", "question01", "A", "B", "C", "D", "D", "this is cap");
		ans[1] = new AnswerMC("category_b", "question02", "A", "B", "C", "D", "D", "this is cap");
		ans[2] = new AnswerMC("category_c", "question03", "A", "B", "C", "D", "D", "this is cap");
		ans[3] = new AnswerMC("category_a", "question03", "A", "B", "C", "D", "D", "this is cap");
		assertTrue(m.insertAnswer(ans[0]));
		assertTrue(m.insertAnswer(ans[1]));
		assertTrue(m.insertAnswer(ans[2]));
		assertTrue(m.insertAnswer(ans[3]));
		BufferedReader br = new BufferedReader(
				new FileReader(new File(FILEPATH_CORRECT)));
		br.readLine(); br.readLine();
		assertEquals(ans[0].toString(), br.readLine());
		assertEquals(ans[1].toString(), br.readLine());
		assertEquals(ans[2].toString(), br.readLine());
		assertEquals(ans[3].toString(), br.readLine());
		br.close();
	}
	
	@Test
	public void insert02() throws IOException {
		assertFalse(m.insertAnswer(new AnswerTF(" ", " ", true, "caption")));
	}
	
	@Test
	public void hasWrongLines01() throws IOException {
		AnswerMC[] ans = new AnswerMC[4];
		ans[0] = new AnswerMC("category_a", "question01", "A", "B", "C", "D", "D", "this is cap");
		ans[1] = new AnswerMC("category_b", "question02", "A", "B", "C", "D", "D", "this is cap");
		ans[2] = new AnswerMC("category_c", "question03", "A", "B", "C", "D", "D", "this is cap");
		ans[3] = new AnswerMC("category_a", "question03", "A", "B", "C", "D", "D", "this is cap");
		assertTrue(m.insertAnswer(ans[0]));
		assertTrue(m.insertAnswer(ans[1]));
		assertTrue(m.insertAnswer(ans[2]));
		assertTrue(m.insertAnswer(ans[3]));		
		assertTrue(!m.hasWrongLines());
		assertTrue(m.isWellFormed());
	}
	
	@Test
	public void hasWrongLines02() throws IOException {
		m.insertAnswer(new AnswerMC("category_a", "sdad", "A", "C", "D", "F", "A", "this is captain america"));
		//append string to file
		FileWriter fw = new FileWriter(FILEPATH_CORRECT, true);
		fw.write("\"dddddddddd\", \"dadasdasd\"" + System.lineSeparator());
		fw.close();
		///////////
		m.insertAnswer(new AnswerMC("category_b", "sdad", "A", "C", "D", "F", "A", "this is captain america"));
		assertTrue(m.hasWrongLines());
		assertFalse(m.isWellFormed());
	}
	
	//readAnswers
	@Test(expected = IllegalArgumentException.class)
	public void readAnswersNull() throws FileNotFoundException, IOException {
		m.readAnswers(null);
	}
	
	@Test
	public void readAnswers01() throws IOException {
		AnswerMC[] ans = new AnswerMC[6];
		ans[0] = new AnswerMC("category_a", "question01", "A", "B", "C", "D", "D", "this is cap");
		ans[1] = new AnswerMC("category_b", "question02", "A", "B", "C", "D", "D", "this is cap");
		ans[2] = new AnswerMC("category_c", "question03", "A", "B", "C", "D", "D", "this is cap");
		ans[3] = new AnswerMC("category_a", "question04", "A", "B", "C", "D", "D", "this is cap");
		ans[4] = new AnswerMC("category_a", "question05", "A", "B", "C", "D", "D", "this is cap");
		ans[5] = new AnswerMC("category_c", "question06", "A", "B", "C", "D", "D", "this is cap");
		m.insertAnswer(ans[0]);
		m.insertAnswer(ans[1]);
		m.insertAnswer(ans[2]);
		m.insertAnswer(ans[3]);
		m.insertAnswer(ans[4]);
		m.insertAnswer(ans[5]);
		//verifichiamo A
		IAnswers[] expA = new AnswerMC[] {ans[0], ans[3], ans[4]};
		IAnswers[] actA = m.readAnswers("category_a");
		assertArrayEquals(expA, actA);
		//verifichiamo B
		IAnswers[] expB = new AnswerMC[] {ans[1]};
		IAnswers[] actB = m.readAnswers("category_b");
		assertArrayEquals(expB, actB);
		//verifichiamo C
		IAnswers[] expC = new AnswerMC[] {ans[2], ans[5]};
		IAnswers[] actC = m.readAnswers("category_c");
		assertArrayEquals(expC, actC);
		//verifichiamo tutti
		assertArrayEquals(ans, m.readAnswers(""));
		//verifichiamo null
		assertNull(m.readAnswers("nessuna_categoria"));
	}
	
	//testiamo quando file è vuoto
	@Test
	public void readAnswer02() throws FileNotFoundException, IOException {
		assertNull(m.readAnswers(""));
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void removeWrongLinesIllegalArg() throws IOException {
		m.setFile(FILEPATH_NOT_CORRECT);
		m.removeWrongLines();
	}
	
	//mi rimuove i problemi
	@Test
	public void removeWrongLines01() throws IOException {
		AnswerMC[] ans = new AnswerMC[6];
		ans[0] = new AnswerMC("category_a", "question01", "A", "B", "C", "D", "D", "this is cap");
		ans[1] = new AnswerMC("category_b", "question02", "A", "B", "C", "D", "D", "this is cap");
		ans[2] = new AnswerMC("category_c", "question03", "A", "B", "C", "D", "D", "this is cap");
		ans[3] = new AnswerMC("category_a", "question04", "A", "B", "C", "D", "D", "this is cap");
		ans[4] = new AnswerMC("category_a", "question05", "A", "B", "C", "D", "D", "this is cap");
		ans[5] = new AnswerMC("category_c", "question06", "A", "B", "C", "D", "D", "this is cap");
		m.insertAnswer(ans[0]);
		m.insertAnswer(ans[1]);
		m.insertAnswer(ans[2]);
		m.insertAnswer(ans[3]);
		//APPEND
		FileWriter fw = new FileWriter(FILEPATH_CORRECT, true);
		fw.write("\"dddddddddd\", \"dadasdasd\"" + System.lineSeparator());
		fw.close();
		///////
		m.insertAnswer(ans[4]);
		m.insertAnswer(ans[5]);
		assertTrue(m.hasWrongLines());
		assertFalse(m.isWellFormed());
		//rimuovi
		assertTrue(m.removeWrongLines());
		assertArrayEquals(ans, m.readAnswers(""));
	}
	
	@Test
	//non mi rimuove niente
	public void removeWrongLines02() throws IOException {
		AnswerMC[] ans = new AnswerMC[6];
		ans[0] = new AnswerMC("category_a", "question01", "A", "B", "C", "D", "D", "this is cap");
		ans[1] = new AnswerMC("category_b", "question02", "A", "B", "C", "D", "D", "this is cap");
		ans[2] = new AnswerMC("category_c", "question03", "A", "B", "C", "D", "D", "this is cap");
		ans[3] = new AnswerMC("category_a", "question04", "A", "B", "C", "D", "D", "this is cap");
		ans[4] = new AnswerMC("category_a", "question05", "A", "B", "C", "D", "D", "this is cap");
		ans[5] = new AnswerMC("category_c", "question06", "A", "B", "C", "D", "D", "this is cap");
		m.insertAnswer(ans[0]);
		m.insertAnswer(ans[1]);
		m.insertAnswer(ans[2]);
		m.insertAnswer(ans[3]);
		m.insertAnswer(ans[4]);
		m.insertAnswer(ans[5]);
		assertTrue(!m.hasWrongLines());
		assertTrue(m.isWellFormed());
		assertFalse(m.removeWrongLines());
		assertArrayEquals(ans, m.readAnswers(""));
	}
	
	@Test
	public void hasWrongLinesConditionTest() throws IOException {
		AnswerMC[] ans = new AnswerMC[4];
		ans[0] = new AnswerMC("category_a", "question01", "A", "B", "C", "D", "A", "this is cap");
		ans[1] = new AnswerMC("category_b", "question02", "A", "B", "C", "D", "B", "this is cap");
		ans[2] = new AnswerMC("category_c", "question03", "A", "B", "C", "D", "C", "this is cap");
		ans[3] = new AnswerMC("category_a", "question03", "A", "B", "C", "D", "D", "this is cap");
		assertTrue(m.insertAnswer(ans[0]));
		assertTrue(m.insertAnswer(ans[1]));
		assertTrue(m.insertAnswer(ans[2]));
		assertTrue(m.insertAnswer(ans[3]));		
		assertTrue(!m.hasWrongLines());
		assertTrue(m.isWellFormed());
		//inserisci uno con 7 strighe corrette ma con risposta sbagliata
		//append string to file
		FileWriter fw = new FileWriter(FILEPATH_CORRECT, true);
		fw.write("\"category_a\",\"question01\",\"A\",\"B\",\"C\",\"D\",\"RispostaCorretta!\",\"this is cap\"" + System.lineSeparator());
		fw.close();
		///////////
		assertTrue(m.hasWrongLines());
		assertTrue(!m.isWellFormed());
	}
	
}
