package junit.model;

import static org.junit.Assert.*;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import org.junit.Before;
import org.junit.Test;

import model.AnswerMC;
import model.AnswerTF;
import model.IAnswers;
import model.TfModel;

public class TfModelTest {

	private static final String FILEPATH_CORRECT = "./test/junit/model/correct_tf.txt";
	private static final String FILEPATH_NOT_CORRECT = "./test/junit/model/not_correct_tf.txt";
	private final String CORRECT_KEYS;
	
//	private BufferedReader br = null;
//	private BufferedWriter bw = null;
	private TfModel m;
	
	public TfModelTest() {
		CORRECT_KEYS = "\"TF\"" + System.lineSeparator() + "\"category\",\"question\",\"answer\",\"caption\"" + System.lineSeparator();
	}
	
	@Before
	public void init() throws IOException {
		//Reset file
		BufferedWriter bw = new BufferedWriter(new FileWriter(FILEPATH_CORRECT));
		bw.write(CORRECT_KEYS);
		bw.close();
		m = new TfModel(FILEPATH_CORRECT);
	}
	
	@Test
	public void hasKey01() throws FileNotFoundException, IOException {
		TfModel m = new TfModel(FILEPATH_NOT_CORRECT);
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
		AnswerTF[] ans = new AnswerTF[4];
		ans[0] = new AnswerTF("category_a", "question01", true, "this is cap");
		ans[1] = new AnswerTF("category_b", "question02", false, "this is cap");
		ans[2] = new AnswerTF("category_c", "question03", true, "this is cap");
		ans[3] = new AnswerTF("category_a", "question03", true, "this is cap");
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
		assertFalse(m.insertAnswer(new AnswerMC("category", "question", "A", "B", "C", "D", "A", "caption")));
	}
	
	@Test
	public void hasWrongLines01() throws IOException {
		AnswerTF[] ans = new AnswerTF[4];
		ans[0] = new AnswerTF("category_a", "question01", true, "this is cap");
		ans[1] = new AnswerTF("category_b", "question02", false, "this is cap");
		ans[2] = new AnswerTF("category_c", "question03", true, "this is cap");
		ans[3] = new AnswerTF("category_a", "question03", true, "this is cap");
		assertTrue(m.insertAnswer(ans[0]));
		assertTrue(m.insertAnswer(ans[1]));
		assertTrue(m.insertAnswer(ans[2]));
		assertTrue(m.insertAnswer(ans[3]));		
		assertTrue(!m.hasWrongLines());
		assertTrue(m.isWellFormed());
	}
	
	@Test
	public void hasWrongLines02() throws IOException {
		m.insertAnswer(new AnswerTF("category_a", "sdad", true, "this is captain america"));
		//append string to file
		FileWriter fw = new FileWriter(FILEPATH_CORRECT, true);
		fw.write("\"dddddddddd\", \"dadasdasd\"" + System.lineSeparator());
		fw.close();
		///////////
		m.insertAnswer(new AnswerTF("category_b", "sdad", false, "this is captain america"));
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
		AnswerTF[] ans = new AnswerTF[6];
		ans[0] = new AnswerTF("category_a", "question01", false, "this is cap");
		ans[1] = new AnswerTF("category_b", "question02", true, "this is cap");
		ans[2] = new AnswerTF("category_c", "question03", true, "this is cap");
		ans[3] = new AnswerTF("category_a", "question04", false, "this is cap");
		ans[4] = new AnswerTF("category_a", "question05", false, "this is cap");
		ans[5] = new AnswerTF("category_c", "question06", false, "this is cap");
		m.insertAnswer(ans[0]);
		m.insertAnswer(ans[1]);
		m.insertAnswer(ans[2]);
		m.insertAnswer(ans[3]);
		m.insertAnswer(ans[4]);
		m.insertAnswer(ans[5]);
		//verifichiamo A
		IAnswers[] expA = new AnswerTF[] {ans[0], ans[3], ans[4]};
		IAnswers[] actA = m.readAnswers("category_a");
		for (IAnswers a : actA) {
			System.out.println(a.toString());
		}
		assertArrayEquals(expA, actA);
		//verifichiamo B
		IAnswers[] expB = new AnswerTF[] {ans[1]};
		IAnswers[] actB = m.readAnswers("category_b");
		assertArrayEquals(expB, actB);
		//verifichiamo C
		IAnswers[] expC = new AnswerTF[] {ans[2], ans[5]};
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
		AnswerTF[] ans = new AnswerTF[6];
		ans[0] = new AnswerTF("category_a", "question01", false, "this is cap");
		ans[1] = new AnswerTF("category_b", "question02", true, "this is cap");
		ans[2] = new AnswerTF("category_c", "question03", false, "this is cap");
		ans[3] = new AnswerTF("category_a", "question04", true, "this is cap");
		ans[4] = new AnswerTF("category_a", "question05", true, "this is cap");
		ans[5] = new AnswerTF("category_c", "question06", false, "this is cap");
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
		AnswerTF[] ans = new AnswerTF[6];
		ans[0] = new AnswerTF("category_a", "question01", false, "this is cap");
		ans[1] = new AnswerTF("category_b", "question02", true, "this is cap");
		ans[2] = new AnswerTF("category_c", "question03", true, "this is cap");
		ans[3] = new AnswerTF("category_a", "question04", false, "this is cap");
		ans[4] = new AnswerTF("category_a", "question05", true, "this is cap");
		ans[5] = new AnswerTF("category_c", "question06", true, "this is cap");
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
		//append string to file
		FileWriter fw = new FileWriter(FILEPATH_CORRECT, true);
		fw.write("\"category_a\",\"question01\",\"RispostaCorretta!\",\"this is cap\"" + System.lineSeparator());
		fw.close();
		///////////
		assertTrue(m.hasWrongLines());
		assertTrue(!m.isWellFormed());
	}

}
