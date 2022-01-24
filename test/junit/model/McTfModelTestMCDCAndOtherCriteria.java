package junit.model;

import static org.junit.Assert.*;

import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;

import org.junit.Test;

import model.AnswerMC;
import model.McModel;
import model.Model;
import model.TfModel;

public class McTfModelTestMCDCAndOtherCriteria {
	
	private static final String MC_NOT_CORRECT = "./test/junit/model/not_correct_mc.txt";
	private static final String TF_NOT_CORRECT = "./test/junit/model/not_correct_tf.txt";
	
	
	@Test(expected = IllegalArgumentException.class)
	public void testMC() throws IOException {
		McModel mc = new McModel(MC_NOT_CORRECT);
		mc.readAnswers("");
	}

	@Test(expected = IllegalArgumentException.class)
	public void testTF() throws IOException {
		Model tf = new TfModel(MC_NOT_CORRECT);
		tf.readAnswers("");
	}
	
}
