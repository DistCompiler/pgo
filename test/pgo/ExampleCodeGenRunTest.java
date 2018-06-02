package pgo;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import org.json.JSONObject;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class ExampleCodeGenRunTest {
	
	private interface JSONMaker{
		void make(JSONObject json);
	}
	
	private static JSONObject json(JSONMaker maker) {
		JSONObject result = new JSONObject();
		maker.make(result);
		return result;
	}

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
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
				Arrays.asList("[24 1 have gcd 1]"),
			},
			{
				Paths.get("Queens.tla"),
				json(root -> {
					JSONObject networking = new JSONObject();
					networking.put("enabled", false);
					root.put("networking", networking);
					
					JSONObject constants = new JSONObject();
					constants.put("N", "1");
					root.put("constants", constants);
				}),
				Arrays.asList(
						"[[1]]"),
			},
			{
				Paths.get("Queens.tla"),
				json(root -> {
					JSONObject networking = new JSONObject();
					networking.put("enabled", false);
					root.put("networking", networking);
					
					JSONObject constants = new JSONObject();
					constants.put("N", "2");
					root.put("constants", constants);
				}),
				Arrays.asList(
						"[]"),
			},
			{
				Paths.get("Queens.tla"),
				json(root -> {
					JSONObject networking = new JSONObject();
					networking.put("enabled", false);
					root.put("networking", networking);
					
					JSONObject constants = new JSONObject();
					constants.put("N", "3");
					root.put("constants", constants);
				}),
				Arrays.asList(
						"[]"),
			},
			{
				Paths.get("Queens.tla"),
				json(root -> {
					JSONObject networking = new JSONObject();
					networking.put("enabled", false);
					root.put("networking", networking);
					
					JSONObject constants = new JSONObject();
					constants.put("N", "4");
					root.put("constants", constants);
				}),
				Arrays.asList(
						"[[2 4 1 3] [3 1 4 2]]"),
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
				Arrays.asList(
						"[[1 3 5 2 4] [1 4 2 5 3] [2 4 1 3 5] [2 5 3 1 4] [3 1 4 2 5]"
						+" [3 5 2 4 1] [4 1 3 5 2] [4 2 5 3 1] [5 2 4 1 3] [5 3 1 4 2]]"),
			},
			{
				Paths.get("Queens.tla"),
				json(root -> {
					JSONObject networking = new JSONObject();
					networking.put("enabled", false);
					root.put("networking", networking);
					
					JSONObject constants = new JSONObject();
					constants.put("N", "9");
					root.put("constants", constants);
				}),
				Arrays.asList(
						"[[1 3 6 8 2 4 9 7 5] [1 3 7 2 8 5 9 4 6] [1 3 8 6 9 2 5 7 4] [1 4 2 8 6 9 3 5 7] [1 4 6 3 9 2 8 5 7] [1 4 6 8 2 5 3 9 7] [1 4 7 3 8 2 5 9 6] [1 4 7 9 2 5 8 6 3] [1 4 8 3 9 7 5 2 6] [1 5 2 6 9 3 8 4 7] [1 5 7 2 6 3 9 4 8] [1 5 7 9 3 8 2 4 6] [1 5 7 9 4 2 8 6 3] [1 5 9 2 6 8 3 7 4] [1 5 9 6 4 2 8 3 7] [1 6 2 9 7 4 8 3 5] [1 6 4 2 7 9 3 5 8] [1 6 4 2 8 3 9 7 5] [1 6 8 3 7 4 2 9 5] [1 6 8 5 2 4 9 7 3] [1 6 9 5 2 8 3 7 4] [1 7 4 6 9 2 5 3 8] [1 7 4 8 3 5 9 2 6] [1 7 4 8 3 9 6 2 5] [1 7 5 8 2 9 3 6 4] [1 8 4 2 7 9 6 3 5] [1 8 5 3 6 9 2 4 7] [1 8 5 3 9 7 2 4 6] [2 4 1 7 9 6 3 5 8] [2 4 7 1 3 9 6 8 5] [2 4 8 3 9 6 1 5 7] [2 4 9 7 3 1 6 8 5] [2 4 9 7 5 3 1 6 8] [2 5 7 1 3 8 6 4 9] [2 5 7 4 1 3 9 6 8] [2 5 7 9 3 6 4 1 8] [2 5 7 9 4 8 1 3 6] [2 5 8 1 3 6 9 7 4] [2 5 8 1 9 6 3 7 4] [2 5 8 6 9 3 1 4 7] [2 5 8 6 9 3 1 7 4] [2 5 9 4 1 8 6 3 7] [2 6 1 3 7 9 4 8 5] [2 6 1 7 4 8 3 5 9] [2 6 1 7 5 3 9 4 8] [2 6 1 9 5 8 4 7 3] [2 6 3 1 8 4 9 7 5] [2 6 9 3 5 8 4 1 7] [2 7 5 1 9 4 6 8 3] [2 7 5 8 1 4 6 3 9] [2 7 9 6 3 1 4 8 5] [2 8 1 4 7 9 6 3 5] [2 8 5 3 9 6 4 1 7] [2 8 6 9 3 1 4 7 5] [2 9 5 3 8 4 7 1 6] [2 9 6 3 5 8 1 4 7] [2 9 6 3 7 4 1 8 5] [2 9 6 4 7 1 3 5 8] [3 1 4 7 9 2 5 8 6] [3 1 6 8 5 2 4 9 7] [3 1 7 2 8 6 4 9 5] [3 1 7 5 8 2 4 6 9] [3 1 8 4 9 7 5 2 6] [3 1 9 7 5 2 8 6 4] [3 5 2 8 1 4 7 9 6] [3 5 2 8 1 7 4 6 9] [3 5 7 1 4 2 8 6 9] [3 5 8 2 9 6 1 7 4] [3 5 8 2 9 7 1 4 6] [3 5 9 2 4 7 1 8 6] [3 5 9 4 1 7 2 6 8] [3 6 2 7 1 4 8 5 9] [3 6 2 9 5 1 8 4 7] [3 6 8 1 4 7 5 2 9] [3 6 8 1 5 9 2 4 7] [3 6 8 2 4 9 7 5 1] [3 6 8 5 1 9 7 2 4] [3 6 8 5 2 9 7 4 1] [3 6 9 1 8 4 2 7 5] [3 6 9 2 5 7 4 1 8] [3 6 9 2 8 1 4 7 5] [3 6 9 5 8 1 4 2 7] [3 6 9 7 1 4 2 5 8] [3 6 9 7 2 4 8 1 5] [3 6 9 7 4 1 8 2 5] [3 7 2 4 8 1 5 9 6] [3 7 2 8 5 9 1 6 4] [3 7 2 8 6 4 1 5 9] [3 7 4 2 9 5 1 8 6] [3 7 4 2 9 6 1 5 8] [3 7 4 8 5 9 1 6 2] [3 7 9 1 5 2 8 6 4] [3 7 9 4 2 5 8 6 1] [3 8 2 4 9 7 5 1 6] [3 8 4 7 9 2 5 1 6] [3 8 6 1 9 2 5 7 4] [3 8 6 4 9 1 5 7 2] [3 8 6 9 2 5 1 4 7] [3 9 2 5 8 1 7 4 6] [3 9 4 1 8 6 2 7 5] [3 9 4 2 8 6 1 7 5] [3 9 4 8 5 2 6 1 7] [3 9 6 2 5 7 1 4 8] [3 9 6 4 1 7 5 2 8] [3 9 6 8 2 4 1 7 5] [4 1 3 6 9 2 8 5 7] [4 1 5 2 9 7 3 8 6] [4 1 5 8 2 7 3 6 9] [4 1 5 9 2 6 8 3 7] [4 1 7 9 2 6 8 3 5] [4 1 9 6 3 7 2 8 5] [4 2 5 8 1 3 6 9 7] [4 2 7 3 1 8 5 9 6] [4 2 7 9 1 5 8 6 3] [4 2 7 9 1 8 5 3 6] [4 2 8 3 9 7 5 1 6] [4 2 9 3 6 8 1 5 7] [4 2 9 5 1 8 6 3 7] [4 6 1 5 2 8 3 7 9] [4 6 1 9 5 8 2 7 3] [4 6 1 9 7 3 8 2 5] [4 6 3 9 2 5 8 1 7] [4 6 3 9 2 8 5 7 1] [4 6 3 9 7 1 8 2 5] [4 6 8 2 5 1 9 7 3] [4 6 8 2 5 7 9 1 3] [4 6 8 2 7 1 3 5 9] [4 6 8 3 1 7 5 2 9] [4 6 9 3 1 8 2 5 7] [4 7 1 3 9 6 8 5 2] [4 7 1 6 9 2 8 5 3] [4 7 1 8 5 2 9 3 6] [4 7 3 6 9 1 8 5 2] [4 7 3 8 2 5 9 6 1] [4 7 3 8 6 1 9 2 5] [4 7 3 8 6 2 9 5 1] [4 7 5 2 9 1 3 8 6] [4 7 5 2 9 1 6 8 3] [4 7 5 2 9 6 8 3 1] [4 7 9 2 5 8 1 3 6] [4 7 9 2 6 1 3 5 8] [4 7 9 6 3 1 8 5 2] [4 8 1 5 7 2 6 3 9] [4 8 5 3 1 6 2 9 7] [4 8 5 3 1 7 2 6 9] [4 9 3 6 2 7 5 1 8] [4 9 5 3 1 6 8 2 7] [4 9 5 3 1 7 2 8 6] [4 9 5 8 1 3 6 2 7] [5 1 6 4 2 8 3 9 7] [5 1 8 4 2 7 9 6 3] [5 1 8 6 3 7 2 4 9] [5 2 4 1 7 9 3 6 8] [5 2 4 9 7 3 1 6 8] [5 2 6 1 3 7 9 4 8] [5 2 6 9 3 8 4 7 1] [5 2 6 9 7 4 1 3 8] [5 2 8 1 4 7 9 6 3] [5 2 8 1 7 9 3 6 4] [5 2 8 3 7 4 1 9 6] [5 2 8 3 7 9 1 6 4] [5 2 9 1 6 8 3 7 4] [5 2 9 6 3 7 4 1 8] [5 3 1 6 2 9 7 4 8] [5 3 1 6 8 2 4 7 9] [5 3 1 7 2 8 6 4 9] [5 3 6 9 2 8 1 4 7] [5 3 6 9 7 1 4 2 8] [5 3 6 9 7 2 4 8 1] [5 3 6 9 7 4 1 8 2] [5 3 8 4 2 9 6 1 7] [5 3 8 4 7 9 2 6 1] [5 3 8 6 2 9 1 4 7] [5 3 8 6 2 9 7 1 4] [5 3 9 4 2 8 6 1 7] [5 3 9 6 8 2 4 1 7] [5 7 1 4 2 8 6 9 3] [5 7 1 6 8 2 4 9 3] [5 7 2 4 8 1 3 9 6] [5 7 2 4 8 1 9 6 3] [5 7 2 6 3 1 8 4 9] [5 7 2 6 8 1 4 9 3] [5 7 4 1 3 6 9 2 8] [5 7 4 1 3 8 6 2 9] [5 7 4 1 3 9 6 8 2] [5 7 4 1 8 2 9 6 3] [5 7 9 3 8 2 4 6 1] [5 7 9 4 2 8 6 3 1] [5 7 9 4 8 1 3 6 2] [5 8 1 4 7 3 6 9 2] [5 8 1 9 4 2 7 3 6] [5 8 2 7 3 1 9 4 6] [5 8 2 7 3 6 9 1 4] [5 8 2 9 3 1 7 4 6] [5 8 2 9 6 3 1 4 7] [5 8 4 1 3 6 9 7 2] [5 8 4 1 7 2 6 3 9] [5 8 4 9 7 3 1 6 2] [5 8 6 1 3 7 9 4 2] [5 8 6 9 3 1 7 4 2] [5 9 2 4 7 3 8 6 1] [5 9 2 6 8 3 1 4 7] [5 9 4 6 8 2 7 1 3] [6 1 5 2 9 7 4 8 3] [6 1 5 7 9 3 8 2 4] [6 1 5 7 9 4 2 8 3] [6 1 7 4 8 3 5 9 2] [6 2 5 7 9 3 8 4 1] [6 2 5 7 9 4 8 1 3] [6 2 9 5 3 8 4 7 1] [6 3 1 4 7 9 2 5 8] [6 3 1 8 4 9 7 5 2] [6 3 1 8 5 2 9 7 4] [6 3 5 8 1 4 2 7 9] [6 3 5 8 1 9 4 2 7] [6 3 5 8 1 9 7 2 4] [6 3 7 2 4 8 1 5 9] [6 3 7 2 4 9 1 8 5] [6 3 7 2 8 5 1 4 9] [6 3 7 4 1 9 2 5 8] [6 3 9 2 5 8 1 7 4] [6 3 9 4 1 8 2 5 7] [6 3 9 7 1 4 2 5 8] [6 4 1 7 9 2 8 5 3] [6 4 2 7 9 3 5 8 1] [6 4 2 8 3 9 7 5 1] [6 4 2 8 5 3 1 9 7] [6 4 2 8 5 9 1 3 7] [6 4 7 1 3 9 2 8 5] [6 4 7 1 8 2 5 3 9] [6 4 7 1 8 5 2 9 3] [6 4 9 1 3 7 2 8 5] [6 4 9 1 5 2 8 3 7] [6 4 9 5 8 2 7 3 1] [6 8 1 5 9 2 4 7 3] [6 8 1 7 4 2 9 5 3] [6 8 2 7 1 3 5 9 4] [6 8 3 1 9 2 5 7 4] [6 8 3 1 9 5 2 4 7] [6 8 3 7 9 2 5 1 4] [6 8 5 2 9 7 4 1 3] [6 9 1 4 7 3 8 2 5] [6 9 3 1 8 4 2 7 5] [6 9 5 1 8 4 2 7 3] [6 9 5 2 8 3 7 4 1] [6 9 5 8 1 3 7 2 4] [6 9 7 4 1 8 2 5 3] [7 1 4 2 8 6 9 3 5] [7 1 4 6 9 3 5 8 2] [7 1 4 8 5 3 9 6 2] [7 1 6 2 5 8 4 9 3] [7 1 6 8 2 4 9 3 5] [7 1 6 9 2 4 8 3 5] [7 1 8 5 2 9 3 6 4] [7 2 4 1 8 5 9 6 3] [7 2 4 6 1 9 5 3 8] [7 2 4 9 1 8 5 3 6] [7 2 6 3 1 8 5 9 4] [7 2 8 6 1 3 5 9 4] [7 3 1 6 8 5 2 4 9] [7 3 1 9 5 8 2 4 6] [7 3 6 2 5 1 9 4 8] [7 3 6 8 1 4 9 5 2] [7 3 6 8 1 5 9 2 4] [7 3 8 2 4 6 9 5 1] [7 3 8 2 5 1 9 4 6] [7 3 8 6 2 9 5 1 4] [7 4 1 3 6 9 2 8 5] [7 4 1 3 8 6 2 9 5] [7 4 1 3 9 6 8 5 2] [7 4 1 5 2 9 6 8 3] [7 4 1 8 2 9 6 3 5] [7 4 1 8 5 3 6 9 2] [7 4 1 9 2 6 8 3 5] [7 4 2 5 8 1 3 6 9] [7 4 2 5 9 1 3 8 6] [7 4 2 8 6 1 3 5 9] [7 4 2 9 5 1 8 6 3] [7 4 2 9 6 3 5 8 1] [7 4 8 1 5 9 2 6 3] [7 4 8 3 9 6 2 5 1] [7 5 1 6 9 3 8 4 2] [7 5 1 8 6 3 9 2 4] [7 5 2 8 1 3 9 6 4] [7 5 2 8 1 4 9 3 6] [7 5 3 9 6 8 2 4 1] [7 5 8 2 9 3 6 4 1] [7 5 8 2 9 6 3 1 4] [7 9 1 3 5 8 2 4 6] [7 9 2 6 1 3 5 8 4] [7 9 3 5 2 8 6 4 1] [7 9 3 8 2 4 6 1 5] [7 9 4 2 5 8 6 1 3] [7 9 6 3 1 8 5 2 4] [8 1 4 6 3 9 7 5 2] [8 1 4 7 3 6 9 2 5] [8 1 4 7 5 2 9 6 3] [8 1 5 7 2 6 3 9 4] [8 2 4 1 7 9 6 3 5] [8 2 5 7 1 4 6 9 3] [8 2 9 6 3 1 4 7 5] [8 3 1 4 7 9 6 2 5] [8 3 5 2 9 6 4 7 1] [8 3 5 9 1 6 4 2 7] [8 4 1 7 5 2 6 9 3] [8 4 7 9 2 6 1 3 5] [8 4 9 1 5 2 6 3 7] [8 4 9 3 5 7 1 6 2] [8 4 9 3 6 2 7 5 1] [8 4 9 7 3 1 6 2 5] [8 5 1 6 9 2 4 7 3] [8 5 2 4 1 7 9 3 6] [8 5 2 4 1 7 9 6 3] [8 5 2 9 1 4 7 3 6] [8 5 2 9 7 4 1 3 6] [8 5 3 1 6 2 9 7 4] [8 5 3 1 7 4 6 9 2] [8 5 3 6 9 7 1 4 2] [8 5 3 9 7 2 4 6 1] [8 6 1 3 5 7 9 4 2] [8 6 1 3 7 9 4 2 5] [8 6 2 7 1 4 9 5 3] [8 6 3 9 7 1 4 2 5] [8 6 9 3 1 4 7 5 2] [9 2 5 7 1 3 8 6 4] [9 2 5 7 4 1 8 6 3] [9 2 6 8 3 1 4 7 5] [9 3 5 2 8 1 7 4 6] [9 3 6 2 7 1 4 8 5] [9 3 6 2 7 5 1 8 4] [9 3 6 4 1 8 5 7 2] [9 4 1 5 8 2 7 3 6] [9 4 2 5 8 6 1 3 7] [9 4 2 7 3 6 8 1 5] [9 4 6 8 2 7 1 3 5] [9 4 6 8 3 1 7 5 2] [9 4 8 1 3 6 2 7 5] [9 5 1 4 6 8 2 7 3] [9 5 1 8 4 2 7 3 6] [9 5 3 1 6 8 2 4 7] [9 5 3 1 7 2 8 6 4] [9 5 3 8 4 7 1 6 2] [9 5 8 4 1 7 2 6 3] [9 6 2 7 1 3 5 8 4] [9 6 3 1 8 5 2 4 7] [9 6 3 7 2 8 5 1 4] [9 6 4 2 8 5 7 1 3] [9 6 4 7 1 8 2 5 3] [9 6 8 2 4 1 7 5 3] [9 7 2 4 1 8 5 3 6] [9 7 3 8 2 5 1 6 4] [9 7 4 2 8 6 1 3 5]]")
			},
		});
	}

	private Path fileName;
	private JSONObject config;
	private List<String> expected;
	
	public ExampleCodeGenRunTest(Path fileName, JSONObject config, List<String> expected) {
		this.fileName = fileName;
		this.config = config;
		this.expected = expected;
	}
	
	@Test
	public void test() throws IOException {
		Path tempDirPath = Files.createTempDirectory("pgotest");
		File tempDir = tempDirPath.toFile();
		Path exampleCodePath = Paths.get("examples").resolve(fileName);
		Path generatedConfigPath = tempDirPath.resolve("config.json");
		
		Path compiledOutputPath = tempDirPath.resolve("test.go");
		try{
			
			// write out config file
			try(BufferedWriter w = Files.newBufferedWriter(generatedConfigPath)){
				// ensure the build info is specified. it never changes so no point
				// in requiring it to be added to each test spec
				JSONObject build = new JSONObject();
				build.put("output_dir", tempDirPath.toString());
				build.put("dest_file", "test.go");
				config.put("build", build);
				
				config.write(w);
			}
			
			// invoke the compiler
			PGoMain.main(new String[] {
					"-c",
					generatedConfigPath.toString(),
					exampleCodePath.toString(),
			});
			
			// display the compiled code for inspection
			Files.lines(compiledOutputPath).forEach(line -> {
				System.out.println("source: "+line);
			});
			
			// try to run the result
			IntegrationTestingUtils.testRunGoCode(compiledOutputPath, expected);
			
		} finally {
			IntegrationTestingUtils.expungeFile(tempDir);
		}
	}
	
}
