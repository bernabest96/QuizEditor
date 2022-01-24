package junit.model;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({TfModelTest.class, McModelTest.class, AnswerMCTest.class, 
	AnswerTFTest.class, AnswerMCTestSTATEMENTBRANCHLOOP.class, McTfModelTestMCDCAndOtherCriteria.class})
public class ModelTestSuite {

}
