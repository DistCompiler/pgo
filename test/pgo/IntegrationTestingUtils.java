package pgo;

import org.json.JSONObject;
import pgo.formatters.IndentingWriter;
import pgo.formatters.TLAExpressionFormattingVisitor;
import pgo.model.tla.TLAExpression;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

public class IntegrationTestingUtils {
	
	private IntegrationTestingUtils() {}

	static class KeyValue {
		private String key;
		private TLAExpression value;

		KeyValue(String key, TLAExpression value) {
			super();
			this.key = key;
			this.value = value;
		}

		String getKey() {
			return key;
		}

		TLAExpression getValue() {
			return value;
		}
	}

	public interface TestRunner<T> {
		void run(T t) throws IOException;
	}

	public interface TestSetup {
		Path setup(Path tempDirPath) throws IOException;
	}

	private static void expungeFile(File file) {
		if (file.isDirectory()) {
			for (File f : file.listFiles()) {
				expungeFile(f);
			}
		}
		if (!file.delete()) {
			System.err.println("WARNING: could not delete file "+file+"; check your temp folder");
		}
	}

	// See testRunGoCode and testRunGoCodeShouldPanic below for runner examples
	static void testCompileFile(Path filePath, Map<String, String> constants, TestRunner<Path> runner)
			throws IOException {
		testCompile(ignored -> filePath, constants, runner);
	}

	// See testRunGoCode and testRunGoCodeShouldPanic below for runner examples
	static void testCompileExpression(TLAExpression result, List<KeyValue> vars, TestRunner<Path> runner)
			throws IOException {
		testCompile(tempDirPath -> {
			Path inputFilePath = tempDirPath.resolve("Test.tla");
			// generate test TLA+ file
			try (BufferedWriter w = Files.newBufferedWriter(inputFilePath);
			     IndentingWriter out = new IndentingWriter(w)) {
				out.write("---- MODULE Test ----");
				out.newLine();
				out.write("EXTENDS Sequences, Integers");
				out.newLine();

				out.write("(* --algorithm Test {");
				out.newLine();
				try (IndentingWriter.Indent i_ = out.indent()) {
					if (!vars.isEmpty()) {
						out.write("variables ");
						try (IndentingWriter.Indent i2_ = out.indentToPosition()) {
							for (KeyValue var : vars) {
								out.write(var.getKey());
								out.write(" = ");
								var.getValue().accept(new TLAExpressionFormattingVisitor(out));
								out.write(";");
								out.newLine();
							}
						}
					}
					out.write("{");
					out.newLine();
					try (IndentingWriter.Indent i2_ = out.indent()) {
						out.write("l: print ");
						result.accept(new TLAExpressionFormattingVisitor(out));
					}
					out.newLine();
					out.write("}");
				}
				out.newLine();
				out.write("}");
				out.newLine();
				out.write("*)");

				out.newLine();
				out.write("====");
			}
			return inputFilePath;
		}, Collections.emptyMap(), runner);
	}

	private static void testCompile(TestSetup setup, Map<String, String> constants, TestRunner<Path> runner)
			throws IOException {
		Path tempDirPath = Files.createTempDirectory("pgotest");
		File tempDir = tempDirPath.toFile();
		Path generatedConfigPath = tempDirPath.resolve("config.json");

		Path compiledOutputPath = tempDirPath.resolve("test.go");
		try {
			Path inputFilePath = setup.setup(tempDirPath);
			// generate config file
			try (BufferedWriter w = Files.newBufferedWriter(generatedConfigPath)) {
				JSONObject config = new JSONObject();

				JSONObject build = new JSONObject();
				build.put("output_dir", tempDirPath.toString());
				build.put("dest_file", "test.go");
				config.put("build", build);

				JSONObject networking = new JSONObject();
				networking.put("enabled", false);
				config.put("networking", networking);

				if (constants.size() > 0) {
					JSONObject consts = new JSONObject();
					constants.forEach(consts::put);
					config.put("constants", consts);
				}

				config.write(w);
			}

			// invoke the compiler
			PGoMain.main(new String[] {
					"-c",
					generatedConfigPath.toString(),
					inputFilePath.toString(),
			});

			// display the compiled code for inspection
			Files.lines(compiledOutputPath).forEach(line -> System.out.println("source: " + line));

			// try to run the compiled Go code, check that it prints the right thing
			runner.run(compiledOutputPath);
		} finally {
			expungeFile(tempDir);
		}
	}

	static void testCompileMPCal(Path spec, String pack, Map<String, String> constants, TestRunner<Path> runner)
			throws IOException {
		Path tempDirPath = Files.createTempDirectory("mpcaltest");
		File tempDir = tempDirPath.toFile();
		Path generatedConfigPath = tempDirPath.resolve("config.json");

		Path compiledOutputPath = tempDirPath.resolve("src/"+pack+"/"+pack+".go");
		try {
			// generate config file
			try (BufferedWriter w = Files.newBufferedWriter(generatedConfigPath)) {
				JSONObject config = new JSONObject();

				JSONObject build = new JSONObject();
				build.put("output_dir", tempDirPath.toString());
				build.put("dest_package", pack);
				config.put("build", build);

				if (constants.size() > 0) {
					JSONObject consts = new JSONObject();
					constants.forEach(consts::put);
					config.put("constants", consts);
				}

				config.write(w);
			}

			// invoke the compiler
			PGoMain.main(new String[] {
					"-c",
					generatedConfigPath.toString(),
					spec.toString(),
			});

			runner.run(compiledOutputPath);
		} finally {
			expungeFile(tempDir);
		}
	}

	static void testRunGoCode(Path codePath, List<String> expected) throws IOException {
		// try to run the compiled Go code, check that it prints the right thing
		ProcessBuilder pb = new ProcessBuilder("go", "run", codePath.toString());
		Process p = pb.start();
		// print stderr in case it says something interesting
		try (InputStream err = p.getErrorStream();
		    InputStreamReader r = new InputStreamReader(err);
		    BufferedReader bw = new BufferedReader(r)) {
			bw.lines().forEach(line -> System.out.println("stderr: "+line));
		}
		try (InputStream results = p.getInputStream();
		    InputStreamReader r = new InputStreamReader(results);
		    BufferedReader bw = new BufferedReader(r)) {
			List<String> lines = bw.lines().collect(Collectors.toList());
			assertThat(lines, is(expected));
		}
	}

	static void testRunGoCodeShouldPanic(Path codePath, List<String> expected) throws IOException {
		// try to run the compiled Go code, check that it panics
		ProcessBuilder pb = new ProcessBuilder("go", "run", codePath.toString());
		Process p = pb.start();
		try (InputStream err = p.getErrorStream();
			InputStreamReader r = new InputStreamReader(err);
			BufferedReader bw = new BufferedReader(r)) {
			List<String> lines = bw.lines().collect(Collectors.toList());
			assertThat(lines.subList(0, expected.size()), is(expected));
		}
	}
}
