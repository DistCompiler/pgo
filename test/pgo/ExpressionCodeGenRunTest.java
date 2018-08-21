package pgo;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.model.tla.TLAExpression;

import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class ExpressionCodeGenRunTest {

	static IntegrationTestingUtils.KeyValue kv(String key, TLAExpression value) {
		return new IntegrationTestingUtils.KeyValue(key, value);
	}

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			// case expression tests
			{
				caseexp(arms(
						arm(binop("=", idexp("a"), num(1)), str("a = 1")),
						arm(binop("=", idexp("a"), num(2)), str("a = 2")),
						arm(binop("=", idexp("a"), num(3)), str("a = 3")),
						arm(binop("=", idexp("a"), num(4)), str("a = 4")),
						arm(binop("=", idexp("a"), num(5)), str("a = 5"))
				), str("a > 5 or a < 0")),
				Arrays.asList(kv("a", num(3))),
				Collections.singletonList("a = 3"),
			},
			{
				caseexp(arms(
						arm(binop("=", idexp("a"), num(1)), str("a = 1")),
						arm(binop("=", idexp("a"), num(2)), str("a = 2")),
						arm(binop("=", idexp("a"), num(3)), str("a = 3")),
						arm(binop("=", idexp("a"), num(4)), str("a = 4")),
						arm(binop("=", idexp("a"), num(5)), str("a = 5"))
				), str("a > 5 or a < 0")),
				Arrays.asList(kv("a", num(11))),
				Collections.singletonList("a > 5 or a < 0"),
			},
			{
				caseexp(arms(
						arm(binop("=", idexp("a"), num(1)), str("a = 1")),
						arm(binop("=", idexp("a"), num(2)), str("a = 2")),
						arm(binop("=", idexp("a"), num(3)), str("a = 3")),
						arm(binop("=", idexp("a"), num(4)), str("a = 4")),
						arm(binop("=", idexp("a"), num(5)), str("a = 5"))
				), null),
				Arrays.asList(kv("a", num(3))),
				Collections.singletonList("a = 3"),
			},
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

	private TLAExpression result;
	private List<IntegrationTestingUtils.KeyValue> vars;
	private List<String> expected;

	public ExpressionCodeGenRunTest(TLAExpression result, List<IntegrationTestingUtils.KeyValue> vars, List<String> expected) {
		this.result = result;
		this.vars = vars;
		this.expected = expected;
	}

	@Test
	public void test() throws IOException {
		// try to run the compiled Go code, check that it prints the right thing
		IntegrationTestingUtils.testCompileExpression(result, vars, compiledOutputPath ->
			IntegrationTestingUtils.testRunGoCode(compiledOutputPath, expected));
	}
}
