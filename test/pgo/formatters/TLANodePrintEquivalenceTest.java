package pgo.formatters;

import static org.junit.Assert.*;

import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.hamcrest.CoreMatchers.*;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAModule;
import pgo.model.tla.TLANode;
import pgo.model.tla.TLAUnit;
import pgo.parser.LexicalContext;
import pgo.parser.ParseFailureException;
import pgo.parser.TLAParser;

import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class TLANodePrintEquivalenceTest {
	
	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{ module("TEST", ids(id("foo"), id("bar")), Collections.emptyList(), Collections.emptyList(), Collections.emptyList()) },
			{ module("TEST", ids(), Collections.emptyList(), Collections.emptyList(), Collections.emptyList()) },
			{ module("TEST", ids(id("aaa")),
					Arrays.asList(
						opdef(false, id("foo"), opdecls(opdecl(id("a")), opdecl(id("b"))),
								num(1)
								)
						),
					Collections.emptyList(),
					Collections.emptyList()
					)
			},
			// this is broken by a hack that forces parsing only the units BEFORE the translation. after / during the
			// translation is not needed in practice. If you want this back, make the TLA+ parser faster.
			/*{ module("TEST", ids(id("aaa")),
					Arrays.asList(
							opdef(false, id("foo"), opdecls(opdecl(id("a")), opdecl(id("b"))),
									num(1)
									)
							),
					Arrays.asList(
							opdef(false, id("a"), opdecls(), num(1))
							),
					Arrays.asList(
							opdef(false, id("b"), opdecls(), num(2))
							)
					)
			},*/
		});
	}
	
	TLANode ast;
	public TLANodePrintEquivalenceTest(TLANode ast) {
		this.ast = ast;
	}

	@Test
	public void test() throws ParseFailureException {
		String str = ast.toString();
		System.out.println(str);
		LexicalContext ctx = new LexicalContext(
				Paths.get("TEST"), String.join(System.lineSeparator(), str.split("\n")));
		TLANode actual;
		if(ast instanceof TLAExpression) {
			actual = TLAParser.readExpression(ctx);
		}else if(ast instanceof TLAModule) {
			List<TLAModule> modules = TLAParser.readModules(ctx);
			actual = modules.get(0);
		}else if(ast instanceof TLAUnit) {
			List<TLAUnit> units = TLAParser.readUnits(ctx);
			actual = units.get(0);
		}else {
			throw new RuntimeException("you can only directly write tests for modules, units and expressions");
		}
		
		assertThat(actual, is(ast));
	}

}
