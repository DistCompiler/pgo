package pgo.parser;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pcal.TLAToken;
import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.model.tla.PGoTLAModule;

@RunWith(Parameterized.class)
public class TLAParserTest {
	
	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{"Euclid", },
			{"QueensPluscal", },
			{"TwoPhaseCommit", },
		});
	}
	
	public String fileName;
	public TLAParserTest(String name) {
		fileName = name;
	}

	@Test
	public void test() throws IOException, PGoTLAParseException, PGoTLALexerException {
		TLALexer lexer = new TLALexer(Paths.get("test", "pluscal", fileName+".tla"));
		
		List<TLAToken> tokens = lexer.readTokens();
		
		List<PGoTLAModule> modules = TLAParser.readModules(tokens.listIterator());
		//System.out.println(modules);
	}

}
