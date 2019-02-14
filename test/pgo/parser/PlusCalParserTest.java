package pgo.parser;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.tla.TLAModule;

import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

@RunWith(Parameterized.class)
public class PlusCalParserTest {
	@Parameterized.Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
				{"Euclid", },
				{"QueensPluscal", },
				{"TwoPhaseCommit", },
				{"AltBitProtocol", },
				{"Sum", },
				{"Await", },
				{"FastMutex", },
				{"pgo2pc", },
		});
	}

	public String fileName;
	public PlusCalParserTest(String name) {
		fileName = name;
	}

	@Test
	public void test() throws IOException, ParseFailureException {
		Path inputFilePath = Paths.get("test", "pluscal", fileName+".tla");
		FileChannel fileChannel = new RandomAccessFile(inputFilePath.toFile(), "r").getChannel();
		MappedByteBuffer buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size());
		// assume UTF-8, though technically TLA+ is ASCII only according to the book
		LexicalContext ctx = new LexicalContext(inputFilePath, StandardCharsets.UTF_8.decode(buffer));

		// basic smoke test, ensure that we at least seem to parse all our example files correctly
		PlusCalParser.readAlgorithm(ctx);
	}
}
