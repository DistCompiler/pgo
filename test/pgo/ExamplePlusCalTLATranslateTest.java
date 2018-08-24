package pgo;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.json.JSONObject;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import javax.xml.bind.annotation.adapters.CollapsedStringAdapter;

@RunWith(Parameterized.class)
public class ExamplePlusCalTLATranslateTest {

	private interface JSONMaker {
		void make(JSONObject json);
	}

	private static JSONObject json(JSONMaker maker) {
		JSONObject result = new JSONObject();
		maker.make(result);
		return result;
	}

	@Parameters
	public static List<Object[]> data() {
		return Arrays.asList(new Object[][]{
				{
						Paths.get("Euclid.tla"),
						json(root -> {
							JSONObject networking = new JSONObject();
							networking.put("enabled", false);
							root.put("networking", networking);

							JSONObject constants = new JSONObject();
							constants.put("N", "5");
							root.put("constants", constants);
						}),
						Collections.singletonList("{24 1 have gcd 1}"),
				},
				{
						Paths.get("Queens.tla"),
						json(root -> {
							JSONObject networking = new JSONObject();
							networking.put("enabled", false);
							root.put("networking", networking);

							JSONObject constants = new JSONObject();
							constants.put("N", "5");
							root.put("constants", constants);
						}),
						Collections.singletonList("{24 1 have gcd 1}"),
				},
		});
	}

	private Path fileName;
	private JSONObject config;
	private List<String> expected;

	public ExamplePlusCalTLATranslateTest(Path fileName, JSONObject config, List<String> expected) {
		this.fileName = fileName;
		this.config = config;
		this.expected = expected;
	}

	@Test
	public void test() throws IOException {
		Path tempDirPath = Files.createTempDirectory("pgotest");
		File tempDir = tempDirPath.toFile();
		Path exampleCodePath = Paths.get("examples").resolve(fileName);
		Path copiedExampleCodePath = tempDirPath.resolve(fileName);
		Path generatedConfigPath = tempDirPath.resolve("config.json");

		try {
			// copy the input file since this mode mutates it
			Files.copy(exampleCodePath, copiedExampleCodePath);

			// write out config file
			try (BufferedWriter w = Files.newBufferedWriter(generatedConfigPath)) {
				// ensure the build info is specified. it never changes so no point
				// in requiring it to be added to each test spec
				JSONObject build = new JSONObject();
				build.put("output_dir", tempDirPath.toString());
				build.put("dest_file", "test.go");
				config.put("build", build);

				config.write(w);
			}

			// invoke the compiler
			PGoMain.main(new String[]{
					"-tlagen",
					"-c",
					generatedConfigPath.toString(),
					copiedExampleCodePath.toString(),
			});

			// display the compiled code for inspection
			Files.lines(copiedExampleCodePath).forEach(line -> {
				System.out.println("result: " + line);
			});

			// try to run the result // no
			//IntegrationTestingUtils.testRunGoCode(compiledOutputPath, expected);

		} finally {
			IntegrationTestingUtils.expungeFile(tempDir);
		}
	}

}
