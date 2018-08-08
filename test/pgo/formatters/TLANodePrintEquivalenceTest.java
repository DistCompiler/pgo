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

import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLANode;
import pgo.model.tla.PGoTLAUnit;
import pgo.parser.LexicalContext;
import pgo.parser.TLAParseException;
import pgo.parser.TLAParser;

import static pgo.model.tla.Builder.*;

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
			{ module("TEST", ids(id("aaa")),
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
			},
		});
	}
	
	PGoTLANode ast;
	public TLANodePrintEquivalenceTest(PGoTLANode ast) {
		this.ast = ast;
	}

	@Test
	public void test() throws TLAParseException {
		String str = ast.toString();
		System.out.println(str);
		LexicalContext ctx = new LexicalContext(
				Paths.get("TEST"), String.join(System.lineSeparator(), str.split("\n")));
		PGoTLANode actual;
		if(ast instanceof PGoTLAExpression) {
			actual = TLAParser.readExpression(ctx);
		}else if(ast instanceof PGoTLAModule) {
			List<PGoTLAModule> modules = TLAParser.readModules(ctx);
			actual = modules.get(0);
		}else if(ast instanceof PGoTLAUnit) {
			List<PGoTLAUnit> units = TLAParser.readUnits(ctx);
			actual = units.get(0);
		}else {
			throw new RuntimeException("you can only directly write tests for modules, units and expressions");
		}
		
		assertThat(actual, is(ast));
	}

}
