package pgo;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

import org.json.JSONObject;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.formatters.IndentingWriter;
import pgo.formatters.PGoTLAExpressionFormattingVisitor;
import pgo.model.tla.PGoTLAExpression;

import static pgo.model.tla.Builder.*;

@RunWith(Parameterized.class)
public class ExpressionCodeGenRunTest {
	
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
	
	static KeyValue kv(String key, PGoTLAExpression value) {
		return new KeyValue(key, value);
	}

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{
				binop("\\union", idexp("lhs"), idexp("rhs")),
				Arrays.asList(kv("lhs", set(num(1), num(2))), kv("rhs", set(num(3)))),
				Arrays.asList("[1 2 3]"),
			},
			{
				binop("\\union", idexp("lhs"), idexp("rhs")),
				Arrays.asList(kv("lhs", set(num(1), num(2))), kv("rhs", set(num(3), num(2)))),
				Arrays.asList("[1 2 3]"),
			},
			{
				binop("\\", idexp("lhs"), idexp("rhs")),
				Arrays.asList(kv("lhs", set(num(1), num(2))), kv("rhs", set(num(3)))),
				Arrays.asList("[1 2]"),
			},
			{
				binop("\\", idexp("lhs"), idexp("rhs")),
				Arrays.asList(kv("lhs", set(num(1), num(2))), kv("rhs", set(num(3), num(2)))),
				Arrays.asList("[1]"),
			},
			// pseudo-lexicographical sorting tests
			{
				idexp("value"),
				Arrays.asList(kv("value", set(set(), set(num(1), num(2)), set(num(2))))),
				Arrays.asList("[[] [2] [1 2]]")
			},
			{
				idexp("value"),
				Arrays.asList(kv("value", set(tuple(), tuple(num(1), num(2)), tuple(num(2))))),
				Arrays.asList("[[] [2] [1 2]]")
			},
			{
				binop("\\union", idexp("lhs"), idexp("rhs")),
				Arrays.asList(
						kv("lhs", set(set(num(5), num(3)), set(num(2)), set(num(1), num(10)))),
						kv("rhs", set(set(), set(num(2), num(2))))),
				Arrays.asList("[[] [2] [1 10] [3 5]]")
			},
			// TODO: fun typing bug(s)
			{
				binop("\\", idexp("lhs"), idexp("rhs")),
				Arrays.asList(
						kv("lhs", set(
								tuple(),
								tuple(num(1)))),
						kv("rhs", set(
								tuple(),
								tuple(num(2)),
								tuple(num(1), num(2))))),
				Arrays.asList("[[1]]"),
			},
			{
				binop("\\", idexp("lhs"), idexp("rhs")),
				Arrays.asList(
						kv("lhs", set(
								tuple(num(1)))),
						kv("rhs", set(
								tuple(num(2)),
								tuple(num(1), num(2))))),
				Arrays.asList("[[1]]"),
			},
			// TODO: even hinting that they should be slices with Append doesn't work
			{
				binop("\\", idexp("lhs"), idexp("rhs")),
				Arrays.asList(
						kv("lhs", set(tuple(), tuple(num(1)))),
						kv("rhs", set(tuple(), tuple(num(2)), tuple(num(1), num(2)))),
						kv("workaround1", opcall("Append", idexp("lhs"), num(5))),
						kv("workaround2", opcall("Append", idexp("rhs"), num(5)))),
				Arrays.asList("[[1]]"),
			},
		});
	}

	private PGoTLAExpression result;
	private List<KeyValue> vars;
	private List<String> expected;
	
	public ExpressionCodeGenRunTest(PGoTLAExpression result, List<KeyValue> vars, List<String> expected) {
		this.result = result;
		this.vars = vars;
		this.expected = expected;
	}
	
	@Test
	public void test() throws IOException {
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
				out.write("EXTENDS Sequences");
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
			
			// try to run the compiled Go code, check that it prints the right thing
			IntegrationTestingUtils.testRunGoCode(compiledOutputPath, expected);
			
		} finally {
			IntegrationTestingUtils.expungeFile(tempDir);
		}
	}
	
}
