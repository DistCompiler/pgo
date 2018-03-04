package pgo.parser;

import java.io.IOException;
import java.net.URL;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
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
		});
	}
	
	public String fileName;
	public TLAParserTest(String name) {
		fileName = name;
	}

	@Test
	public void test() throws IOException, PGoTLAParseException, PGoTLALexerException {
		Class<? extends TLAParserTest> c = getClass();
		FileSystem fs = FileSystems.getDefault();
		
		URL tlaName = c.getResource("../../pluscal/"+fileName+".tla");
		TLALexer lexer = new TLALexer(fs.getPath(tlaName.getFile()));
		
		List<TLAToken> tokens = lexer.readTokens();
		
		List<PGoTLAModule> modules = TLAParser.readModules(tokens.listIterator());
		//System.out.println(modules);
	}

}
