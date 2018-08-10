package pgo;

import org.json.JSONObject;
import pgo.formatters.IndentingWriter;
import pgo.formatters.PGoTLAExpressionFormattingVisitor;
import pgo.model.tla.PGoTLAExpression;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;

public class IntegrationTestingUtils {
	
	private IntegrationTestingUtils() {}

	static class KeyValue {
		private String key;
		private PGoTLAExpression value;

		public KeyValue(String key, PGoTLAExpression value) {
			super();
			this.key = key;
			this.value = value;
		}

		public String getKey() {
			return key;
		}

		public PGoTLAExpression getValue() {
			return value;
		}
	}
	
	public static void expungeFile(File file) {
		if(file.isDirectory()) {
			for(File f : file.listFiles()) {
				expungeFile(f);
			}
		}
		if(!file.delete()) {
			System.err.println("WARNING: could not delete file "+file+"; check your temp folder");
		}
	}

	public static void testCompileExpression(PGoTLAExpression result, List<KeyValue> vars,
											 List<String> expected, Boolean panic) throws IOException {
		Path tempDirPath = Files.createTempDirectory("pgotest");
		File tempDir = tempDirPath.toFile();
		Path generatedCodePath = tempDirPath.resolve("Test.tla");
		Path generatedConfigPath = tempDirPath.resolve("config.json");

		Path compiledOutputPath = tempDirPath.resolve("test.go");
		try{
			// generate test TLA+ file
			try(BufferedWriter w = Files.newBufferedWriter(generatedCodePath);
				IndentingWriter out = new IndentingWriter(w);){
				out.write("---- MODULE Test ----");
				out.newLine();
				out.write("EXTENDS Sequences, Integers");
				out.newLine();

				out.write("(* --algorithm Test {");
				out.newLine();
				try(IndentingWriter.Indent i_ = out.indent()){
					if(!vars.isEmpty()) {
						out.write("variables ");
						try(IndentingWriter.Indent i2_ = out.indentToPosition()){
							for(KeyValue var : vars) {
								out.write(var.getKey());
								out.write(" = ");
								var.getValue().accept(new PGoTLAExpressionFormattingVisitor(out));
								out.write(";");
								out.newLine();
							}
						}
					}
					out.write("{");
					out.newLine();
					try(IndentingWriter.Indent i2_ = out.indent()){
						out.write("print ");
						result.accept(new PGoTLAExpressionFormattingVisitor(out));
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

			// generate config file
			try(BufferedWriter w = Files.newBufferedWriter(generatedConfigPath)){
				JSONObject config = new JSONObject();

				JSONObject build = new JSONObject();
				build.put("output_dir", tempDirPath.toString());
				build.put("dest_file", "test.go");
				config.put("build", build);

				JSONObject networking = new JSONObject();
				networking.put("enabled", false);
				config.put("networking", networking);

				config.write(w);
			}

			// invoke the compiler
			PGoMain.main(new String[] {
					"-c",
					generatedConfigPath.toString(),
					generatedCodePath.toString(),
			});

			// display the compiled code for inspection
			Files.lines(compiledOutputPath).forEach(line -> {
				System.out.println("source: "+line);
			});

			System.out.println("Got here ok");

			// try to run the compiled Go code, check that it prints the right thing
			if (!panic) {
				IntegrationTestingUtils.testRunGoCode(compiledOutputPath, expected);
			} else {
				IntegrationTestingUtils.testRunGoCodeShouldPanic(compiledOutputPath, expected);
			}
		} finally {
			IntegrationTestingUtils.expungeFile(tempDir);
		}
	}
	
	public static void testRunGoCode(Path codePath, List<String> expected) throws IOException {
		// try to run the compiled Go code, check that it prints the right thing
		ProcessBuilder pb = new ProcessBuilder("go", "run", codePath.toString());
		Process p = pb.start();
		// print stderr in case it says something interesting
		try(InputStream err = p.getErrorStream();
				InputStreamReader r = new InputStreamReader(err);
				BufferedReader bw = new BufferedReader(r)){
			bw.lines().forEach(line -> {
				System.out.println("stderr: "+line);
			});
		}
		try(InputStream results = p.getInputStream();
				InputStreamReader r = new InputStreamReader(results);
				BufferedReader bw = new BufferedReader(r)){
			List<String> lines = bw.lines().collect(Collectors.toList());
			assertThat(lines, is(expected));
		}
	}

	public static void testRunGoCodeShouldPanic(Path codePath, List<String> expected) throws IOException {
		// try to run the compiled Go code, check that it panics
		ProcessBuilder pb = new ProcessBuilder("go", "run", codePath.toString());
		Process p = pb.start();
		try(InputStream err = p.getErrorStream();
			InputStreamReader r = new InputStreamReader(err);
			BufferedReader bw = new BufferedReader(r)){
			List<String> lines = bw.lines().collect(Collectors.toList());
			assertThat(lines.subList(0, expected.size()), is(expected));
		}
	}

}
