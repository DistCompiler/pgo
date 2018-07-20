package pgo.parser;

import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
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
		FileChannel fileChannel = new RandomAccessFile(inputFilePath.toFile(), "r").getChannel();
		MappedByteBuffer buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
		// assume UTF-8, though technically TLA+ is ASCII only according to the book
		ParseContext ctx = new ParseContext(inputFilePath, StandardCharsets.UTF_8.decode(buffer));
		
		List<PGoTLAModule> modules = TLAParser.readModules(ctx);
		
		assertThat(modules.size(), is(1));
	}

}
