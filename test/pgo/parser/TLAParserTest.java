package pgo.parser;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.hamcrest.CoreMatchers.*;
import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.lexer.TLAToken;
import pgo.model.tla.PGoTLAModule;

@RunWith(Parameterized.class)
public class TLAParserTest {
	
	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{"Euclid", },
			{"QueensPluscal", },
			{"TwoPhaseCommit", },
			{"AltBitProtocol", },
			{"Sum", },
			{"Await", },
			{"FastMutexNoAnnotation", },
		});
	}
	
	public String fileName;
	public TLAParserTest(String name) {
		fileName = name;
	}

	@Test
	public void test() throws IOException, PGoTLALexerException, TLAParseException {
		Path inputFilePath = Paths.get("test", "pluscal", fileName+".tla");
		List<String> lines = Collections.unmodifiableList(Files.readAllLines(inputFilePath, Charset.forName("utf-8")));
		TLALexer lexer = new TLALexer(inputFilePath, lines);
		
		List<TLAToken> tokens = lexer.readTokens();
		
		List<PGoTLAModule> modules = TLAParser.readModules(tokens.listIterator());
		
		assertThat(modules.size(), is(1));
	}

}
