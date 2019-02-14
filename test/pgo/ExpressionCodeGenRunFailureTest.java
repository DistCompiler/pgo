package pgo;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import pgo.model.tla.TLAExpression;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class ExpressionCodeGenRunFailureTest {
	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			// if expression tests
			{
					caseexp(arms(arm(bool(false), str("Hello world"))), null),
					Collections.emptyList(),
					Collections.singletonList("panic: No matching case!"),
			},
		});
	}

	private TLAExpression result;
	private List<IntegrationTestingUtils.KeyValue> vars;
	private List<String> expected;

	public ExpressionCodeGenRunFailureTest(TLAExpression result, List<IntegrationTestingUtils.KeyValue> vars, List<String> expected) {
		this.result = result;
		this.vars = vars;
		this.expected = expected;
	}

	@Test
	public void test() throws IOException {
		// try to run the compiled Go code, check that it prints the right thing
		IntegrationTestingUtils.testCompileExpression(result, vars, compiledOutputPath ->
			IntegrationTestingUtils.testRunGoCodeShouldPanic(compiledOutputPath, expected));
	}
}
