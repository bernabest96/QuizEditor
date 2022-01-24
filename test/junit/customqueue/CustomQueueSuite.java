package junit.customqueue;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({CustomQueueCapacityTest.class, CustomQueueFunctionalityTest.class, CustomQueueStatementTest.class})
public class CustomQueueSuite {

}
