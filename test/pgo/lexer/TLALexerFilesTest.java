package pgo.lexer;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URL;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Errors;
import tla2sany.modanalyzer.ParseUnit;
import util.NamedInputStream;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pcal.TLAToken;

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
	public void test() throws IOException {
		Class<? extends TLALexerFilesTest> c = getClass();
		FileSystem fs = FileSystems.getDefault();
		
		URL tlaName = c.getResource("../../pluscal/"+fileName+".tla");
		TLALexer lexer = new TLALexer(fs.getPath(tlaName.getFile()));
		
		List<TLAToken> tokens = lexer.readTokens();
		
		URL expectedName = c.getResource("../../tla/tokens/"+fileName+".tokens");
		List<String> expected = Files.readAllLines(fs.getPath(expectedName.getFile()));
		
		assertThat(tokens.stream()
				.map(tok -> tok != null ? tok.toString() : "null")
				.collect(Collectors.toList()), is(expected));
	}

}
