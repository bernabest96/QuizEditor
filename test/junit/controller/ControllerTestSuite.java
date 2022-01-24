package junit.controller;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({ ControllerMCTest.class, ControllerTFTest.class, ControllerSearchTest.class, 
	ControllerInsertMCTestMCDC.class, ControllerInsertTFTestMCDC.class})
public class ControllerTestSuite {

}
