package pgo.trans.intermediate;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.model.pcal.Algorithm;

import static pgo.model.pcal.Builder.*;
import static pgo.model.tla.Builder.*;

@RunWith(Parameterized.class)
public class PlusCalMacroExpansionPassTest {

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{
				algorithm(
						"Test",
						Collections.emptyList(),
						Arrays.asList(
								macro("mymacro", Arrays.asList("a"),
										printS(idexp("a")),
										printS(idexp("b"))
										)
								),
						Collections.emptyList(),
						Collections.emptyList(),
						labeled(label("foo"),
								printS(idexp("a")),
								macroCall("mymacro", binop("+", num(2), num(2)))
								)
						),
				algorithm(
						"Test",
						Collections.emptyList(),
						Collections.emptyList(),
						Collections.emptyList(),
						Collections.emptyList(),
						labeled(label("foo"),
								printS(idexp("a")),
								printS(binop("+", num(2), num(2))),
								printS(idexp("b"))
								)
						)
			},
		});
	}

	private Algorithm before;
	private Algorithm expected;
	
	public PlusCalMacroExpansionPassTest(Algorithm before, Algorithm expected) {
		this.before = before;
		this.expected = expected;
	}
	
	@Test
	public void test() {
		IssueContext ctx = new TopLevelIssueContext();
		Algorithm after = PlusCalMacroExpansionPass.perform(ctx, before);
		assertThat(after, is(expected));
	}

}
