import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import junit.controller.ControllerTestSuite;
import junit.customqueue.CustomQueueSuite;
import junit.model.ModelTestSuite;
import view.CustomQueue;

@RunWith(Suite.class)
@SuiteClasses({ControllerTestSuite.class, CustomQueueSuite.class, ModelTestSuite.class})
public class AllTests {

}
