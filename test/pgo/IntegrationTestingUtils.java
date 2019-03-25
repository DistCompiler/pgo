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
import java.util.*;
import java.util.stream.Collectors;

public class IntegrationTestingUtils {

	static class MPCalRunDefinition {
		private final String identifier;
		private final List<String> args;
		private final List<String> expectedOutput;

		MPCalRunDefinition(String identifier, List<String> args, List<String> expectedOutput) {
			this.identifier = identifier;
			this.args = args;
			this.expectedOutput = expectedOutput;
		}

		String getIdentifier() {
			return identifier;
		}

		List<String> getArgs() {
			return args;
		}

		List<String> getExpectedOutput() {
			return expectedOutput;
		}
	}

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
				out.write("EXTENDS Sequences, FiniteSets, Integers");
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

			runner.run(tempDirPath);
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

	static MPCalRunDefinition mpcalRunDef(String id, List<String> args, List<String> output) {
		return new MPCalRunDefinition(id, args, output);
	}

	private static List<String> runAndPrint(ProcessBuilder pb, String prefix, boolean checkSuccess) {
		try {
			List<String> lines = new ArrayList<>();
			Process build = pb.start();

			try (InputStream err = build.getErrorStream();
				 InputStreamReader r = new InputStreamReader(err);
				 BufferedReader br = new BufferedReader(r)) {

				br.lines().forEach(line -> System.out.println(prefix + ": " + line));
			}

			try (InputStream err = build.getInputStream();
				 InputStreamReader r = new InputStreamReader(err);
				 BufferedReader br = new BufferedReader(r)) {

				br.lines().forEach(lines::add);
			}

			try {
				int exitCode = build.waitFor();
				if (checkSuccess) {
					assertThat(exitCode, is(0));
				}
			} catch (InterruptedException e) {
				throw new RuntimeException("Interrupted: " + e.getMessage());
			}

			return lines;
		} catch (IOException e) {
			throw new RuntimeException("IOException: " + e.getMessage());
		}
	}

	private static List<String> runAndPrint(ProcessBuilder pb, String prefix) {
		return runAndPrint(pb, prefix, true);
	}

	static void testRunDistributedMPCal(Path codePath, List<MPCalRunDefinition> runDefinitions) throws InterruptedException {
		// compile generate code
		String binary = "mpcal_output";

		// TODO: get rid of `go get` once we remove dependency on etcd
		ProcessBuilder pb = new ProcessBuilder("go", "get");
		pb.environment().put("GOPATH", codePath.toString());
		pb.directory(codePath.toFile());
		runAndPrint(pb, "build", false);

		pb = new ProcessBuilder("go", "build", "-v", "-o", binary);
		pb.environment().put("GOPATH", codePath.toString());
		pb.directory(codePath.toFile());

		runAndPrint(pb, "build");

		// run the resulting code according to runDefinitions
		Map<String, List<String>> outputs = new HashMap<>();
		List<Thread> runs = new ArrayList<>();
		runDefinitions.forEach(def ->
			runs.add(new Thread(() -> {
				List<String> command = new ArrayList<>();
				command.add(codePath.resolve(binary).toString());
				command.addAll(def.getArgs());

				System.out.println("Running: " + String.join(" ", command));
				ProcessBuilder builder = new ProcessBuilder(command);
				builder.directory(codePath.toFile());

				outputs.put(def.getIdentifier(), runAndPrint(builder, def.getIdentifier()));
			}))
		);

		for (Thread t : runs) {
			t.start();
		}

		long tenSeconds = 10 * 1000;
		for (Thread t : runs) {
			t.join(tenSeconds);
		}

		runDefinitions.forEach(def -> {
			// compare lines instead of collections for easier debugging
			// if the test fails
			String actual = String.join("\n", outputs.get(def.getIdentifier()));
			String expected = String.join("\n", def.getExpectedOutput());

			assertThat(actual, is(expected));
		});
	}
}
