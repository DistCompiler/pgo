package pgo;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
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
			// if expression tests
			{
				ifexp(bool(true), str("Then Branch"), str("Else Branch")),
				Arrays.asList(),
				Collections.singletonList("Then Branch"),
			},
			{
					ifexp(bool(false), str("Then Branch"), str("Else Branch")),
					Arrays.asList(),
					Collections.singletonList("Else Branch"),
			},
			{
				ifexp(binop(">", idexp("a"), idexp("b")), idexp("a"), idexp("b")),
				Arrays.asList(
						kv("a", num(3)),
						kv("b", num(1))),
				Collections.singletonList("3"),
			},
			{
				ifexp(bool(false), str("Then Branch"), ifexp(bool(true), str("Else Branch -> Then Branch"), str("Else Branch -> Else Branch"))),
				Arrays.asList(),
				Collections.singletonList("Else Branch -> Then Branch"),
			},
			// operator precedence tests
			{
				binop("*", idexp("a"), binop("+", idexp("b"), idexp("c"))),
				Arrays.asList(
						kv("a", num(2)),
						kv("b", num(2)),
						kv("c", num(3))),
				Collections.singletonList("10"),
			},
			{
				binop("*", idexp("a"), binop("+", idexp("b"), binop("*", idexp("c"), idexp("c")))),
				Arrays.asList(
						kv("a", num(2)),
						kv("b", num(2)),
						kv("c", num(3))),
				Collections.singletonList("22"),
			},
			// set construction
			{
				binop("..", num(0), binop("-", idexp("a"), num(1))),
				Collections.singletonList(kv("a", num(10))),
				Collections.singletonList("[0 1 2 3 4 5 6 7 8 9]"),
			},
			// set op tests
			{
				binop("\\union", idexp("lhs"), idexp("rhs")),
				Arrays.asList(kv("lhs", set(num(1), num(2))), kv("rhs", set(num(3)))),
				Collections.singletonList("[1 2 3]"),
			},
			{
				binop("\\union", idexp("lhs"), idexp("rhs")),
				Arrays.asList(kv("lhs", set(num(1), num(2))), kv("rhs", set(num(3), num(2)))),
				Collections.singletonList("[1 2 3]"),
			},
			{
				binop("\\", idexp("lhs"), idexp("rhs")),
				Arrays.asList(kv("lhs", set(num(1), num(2))), kv("rhs", set(num(3)))),
				Collections.singletonList("[1 2]"),
			},
			{
				binop("\\", idexp("lhs"), idexp("rhs")),
				Arrays.asList(kv("lhs", set(num(1), num(2))), kv("rhs", set(num(3), num(2)))),
				Collections.singletonList("[1]"),
			},
			// pseudo-lexicographical sorting tests
			{
				idexp("value"),
				Collections.singletonList(kv("value", set(set(), set(num(1), num(2)), set(num(2))))),
				Collections.singletonList("[[] [2] [1 2]]")
			},
			{
				idexp("value"),
				Arrays.asList(
						kv("workaround", opcall("Append", tuple(), num(2))),
						kv("value", set(tuple(), tuple(num(1), num(2)), idexp("workaround")))),
				Collections.singletonList("[[] [2] [1 2]]")
			},
			{
				binop("\\union", idexp("lhs"), idexp("rhs")),
				Arrays.asList(
						kv("lhs", set(set(num(5), num(3)), set(num(2)), set(num(1), num(10)))),
						kv("rhs", set(set(), set(num(2), num(2))))),
				Collections.singletonList("[[] [2] [1 10] [3 5]]")
			},
			{
				binop("\\", idexp("lhs"), idexp("rhs")),
				Arrays.asList(
						kv("workaround1", opcall("Append", tuple(), num(1))),
						kv("workaround2", opcall("Append", tuple(), num(2))),
						kv("lhs", set(tuple(), idexp("workaround1"))),
						kv("rhs", set(tuple(), idexp("workaround2"), tuple(num(1), num(2))))),
				Collections.singletonList("[[1]]"),
			},
			// function tests
			{
				function(
						bounds(qbIds(ids(id("x")), set(num(1), num(2), num(3)))),
						idexp("x")),
				Collections.emptyList(),
				Collections.singletonList("[{1 1} {2 2} {3 3}]"),
			},
			{
				fncall(idexp("fn"), num(2)),
				Collections.singletonList(
						kv("fn", function(
								bounds(qbIds(ids(id("x")), set(num(1), num(2), num(3)))),
								binop("+", idexp("x"), num(1))))),
				Collections.singletonList("3"),
			},
			// TODO: chokes on codegen
			{
				fncall(idexp("fn"), num(2), num(5)),
				Collections.singletonList(
						kv("fn", function(
								bounds(
										qbIds(
												ids(id("x")),
												set(num(1), num(2), num(3))),
										qbIds(
												ids(id("y")),
												set(num(4), num(5), num(6)))),
								binop("+", idexp("x"), idexp("y"))))),
				Collections.singletonList("7"),
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

			// try to run the compiled Go code, check that it prints the right thing
			IntegrationTestingUtils.testRunGoCode(compiledOutputPath, expected);

		} finally {
			IntegrationTestingUtils.expungeFile(tempDir);
		}
	}

}
