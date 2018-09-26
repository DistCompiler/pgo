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
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.trans.passes.expansion.ModularPlusCalExpansionPass;

import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class ModularPlusCalExpansionPassTest {

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{
				algorithm(
						"Test",
						Collections.emptyList(),
						Collections.singletonList(
								macro("mymacro", Collections.singletonList("a"),
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

	private ModularPlusCalBlock before;
	private ModularPlusCalBlock expected;

	public ModularPlusCalExpansionPassTest(PlusCalAlgorithm before, PlusCalAlgorithm expected) {
		this.before = ModularPlusCalBlock.from(before);
		this.expected = ModularPlusCalBlock.from(expected);
	}
	
	@Test
	public void test() {
		IssueContext ctx = new TopLevelIssueContext();
		ModularPlusCalBlock after = ModularPlusCalExpansionPass.perform(ctx, before);
		assertThat(after, is(expected));
	}

}
