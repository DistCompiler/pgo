package pgo.lexer;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

/**
 * A coarse regression test mainly designed to alert anyone if 
 * the output of the lexer changes. Establishes expected outputs
 * for some common testing specifications.
 */
@RunWith(Parameterized.class)
public class TLALexerFilesTest {

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{"Euclid", },
			{"AltBitProtocol", },
			{"TwoPhaseCommit", },
		});
	}
	
	public String fileName;
	public TLALexerFilesTest(String name) {
		fileName = name;
	}
	
	@Test
	public void test() throws IOException, PGoTLALexerException {
		TLALexer lexer = new TLALexer(Paths.get("test", "pluscal", fileName+".tla"));
		
		List<TLAToken> tokens = lexer.readTokens();
		
		List<String> expected = Files.readAllLines(
				Paths.get("test", "tla", "tokens", fileName+".tokens"));
		
		System.out.println(tokens.stream().reduce("", (String acc, TLAToken tok) -> acc + tok + "\n", (l, r) -> l+r));
		
		assertThat(tokens.stream()
				.map(tok -> tok != null ? tok.toString() : "null")
				.collect(Collectors.toList()), is(expected));
	}

}
