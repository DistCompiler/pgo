package pgo.parser;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.lexer.TLAToken;
import pgo.model.tla.PGoTLAUnit;

import static pgo.model.tla.Builder.*;

@RunWith(Parameterized.class)
public class TLAUnitParseTest {

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{"IsSolution(queens) ==\n" + 
					"  \\A i \\in 1 .. Len(queens)-1 : \\A j \\in i+1 .. Len(queens) :\n" + 
					"       ~ Attacks(queens,i,j)",
					opdef(false, id("IsSolution"), opdecls(opdecl(id("queens"))),
							universal(bounds(qbIds(ids(id("i")), binop("..", num(1), binop("-", opcall("Len", idexp("queens")), num(1))))),
									universal(bounds(qbIds(ids(id("j")), binop("..", binop("+", idexp("i"), num(1)), opcall("Len", idexp("queens"))))),
											unary("~", opcall("Attacks", idexp("queens"), idexp("i"), idexp("j"))))))
			},
			{"Solutions == { queens \\in [1..N -> 1..N] : IsSolution(queens) }",
				opdef(false, id("Solutions"), opdecls(),
						setRefinement("queens", functionSet(binop("..", num(1), idexp("N")), binop("..", num(1), idexp("N"))), opcall("IsSolution", idexp("queens"))))
			}
		});
	}
	
	private String unitString;
	private PGoTLAUnit unitExpected;
	public TLAUnitParseTest(String unitString, PGoTLAUnit unitExpected) {
		this.unitString = unitString;
		this.unitExpected = unitExpected;
	}
	
	static Path testFile = Paths.get("TEST");

	@Test
	public void test() throws PGoTLALexerException, TLAParseException {
		TLALexer lexer = new TLALexer(testFile, Arrays.asList(unitString.split("\n")));
		// don't ignore the expression because it's not in a module
		lexer.requireModule(false);
		
		List<TLAToken> tokens = lexer.readTokens();
		
		System.out.println(tokens);
		
		PGoTLAUnit unit = TLAParser.readUnit(tokens.listIterator());
		
		assertThat(unit, is(unitExpected));
	}

}
