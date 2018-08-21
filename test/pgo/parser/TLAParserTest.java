package pgo.parser;

import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import static org.hamcrest.CoreMatchers.*;
import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.model.tla.TLAModule;

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
				//{"PlusCalAwait", },
				{"FastMutexNoAnnotation", },
				{"pgo2pc", },
		});
	}
	
	public String fileName;
	public TLAParserTest(String name) {
		fileName = name;
	}

	@Test
	public void test() throws IOException, ParseFailureException {
		Path inputFilePath = Paths.get("test", "pluscal", fileName+".tla");
		FileChannel fileChannel = new RandomAccessFile(inputFilePath.toFile(), "r").getChannel();
		MappedByteBuffer buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
		// assume UTF-8, though technically TLA+ is ASCII only according to the book
		LexicalContext ctx = new LexicalContext(inputFilePath, StandardCharsets.UTF_8.decode(buffer));
		
		List<TLAModule> modules = TLAParser.readModules(ctx);
		
		assertThat(modules.size(), is(1));
	}

}
