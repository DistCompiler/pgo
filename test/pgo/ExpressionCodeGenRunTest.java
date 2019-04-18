package pgo;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.json.JSONObject;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.model.tla.TLAExpression;

import static pgo.IntegrationTestingUtils.*;
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
			{
				binop("\\in", idexp("x"), idexp("s")),
				Arrays.asList(kv("x", num(3)), kv("s", set(num(1), num(3), num(2)))),
				Collections.singletonList("true")
			},
			{
					binop("\\in", idexp("x"), idexp("s")),
					Arrays.asList(kv("x", num(30)), kv("s", set(num(1), num(3), num(2)))),
					Collections.singletonList("false")
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
			// set of records: comparisons
			{
				// [a |-> 1, b |-> 2] \in {[a |-> 1, b |-> 2], [a |-> 2, b |-> 1]} ;; TRUE
				binop(
						"\\in",
						record(field(id("a"), num(1)), field(id("b"), num(2))),
						set(idexp("r1"), idexp("r2"))
				),
				Arrays.asList(
						kv("r1", record(field(id("a"), num(1)), field(id("b"), num(2)))),
						kv("r2", record(field(id("a"), num(2)), field(id("b"), num(1))))
				),
				Collections.singletonList("true"),
			},
			{
				// [a |-> 1, b |-> 2] \in {[a |-> 2, b |-> 1], [a |-> 1, b |-> 2]} ;; TRUE
				binop(
						"\\in",
						record(field(id("a"), num(1)), field(id("b"), num(2))),
						set(idexp("r2"), idexp("r1"))
				),
				Arrays.asList(
						kv("r1", record(field(id("a"), num(1)), field(id("b"), num(2)))),
						kv("r2", record(field(id("a"), num(2)), field(id("b"), num(1))))
				),
				Collections.singletonList("true"),
			},
			{
				// [a |-> 1, b |-> "hi"] \in {[a |-> 1, b |-> "nope"], [a |-> 1, b |-> "hi"]} ;; TRUE
				binop(
						"\\in",
						record(field(id("a"), num(1)), field(id("b"), str("hi"))),
						set(idexp("r1"), idexp("r2"))
				),
				Arrays.asList(
						kv("r1", record(field(id("a"), num(1)), field(id("b"), str("nope")))),
						kv("r2", record(field(id("a"), num(1)), field(id("b"), str("hi"))))
				),
				Collections.singletonList("true"),
			},
				{
				// [a |-> 1, b |-> 2] \in {[a |-> 10, b |-> 20], [a |-> 20, b |-> 10]} ;; FALSE
				binop(
						"\\in",
						record(field(id("a"), num(1)), field(id("b"), num(2))),
						set(idexp("r1"), idexp("r2"))
				),
				Arrays.asList(
						kv("r1", record(field(id("a"), num(10)), field(id("b"), num(20)))),
						kv("r2", record(field(id("a"), num(20)), field(id("b"), num(10))))
				),
				Collections.singletonList("false"),
			},
			{
				// [a |-> 1, b |-> 2] \in {} ;; FALSE
				binop(
						"\\in",
						record(field(id("a"), num(1)), field(id("b"), num(2))),
						set()
				),
				Collections.emptyList(),
				Collections.singletonList("false"),
			},

				// quantified universals
			{
				universal(
						bounds(
								qbIds(ids(id("x")), idexp("set1")),
								qbIds(ids(id("y")), idexp("set2"))),
						binop("=",
								binop("%", binop("+", idexp("x"), idexp("y")), num(2)),
								num(1))),
				Arrays.asList(
						kv("set1", set(num(2), num(4), num(6))),
						kv("set2", set(num(1), num(3), num(5)))),
				Collections.singletonList("true"),
			},
			{
				universal(
						bounds(
								qbIds(ids(id("x")), idexp("set")),
								qbIds(ids(id("y")), binop("..", num(1), num(3)))),
						binop("=",
								binop("%", binop("+", idexp("x"), idexp("y")), num(2)),
								num(1))),
				Collections.singletonList(
						kv("set", set(num(2), num(4), num(6)))),
				Collections.singletonList("false"),
			},
			{
				binop("\\o", idexp("seq"), tuple(num(10))),
				Collections.singletonList(kv("seq", tuple(num(1), num(2)))),
				Collections.singletonList("[1 2 10]")
			},
			{
				binop("\\o", idexp("seq"), tuple(num(10))),
				Collections.singletonList(kv("seq", tuple())),
				Collections.singletonList("[10]")
			},
			{
				binop("\\o", binop("\\o", tuple(num(1), num(2)),tuple( num(3))), tuple(num(10), num(11))),
				Collections.emptyList(),
				Collections.singletonList("[1 2 3 10 11]")
			},
			{
                opcall("SubSeq", idexp("seq"), num(4), num(5)),
				Collections.singletonList(kv("seq", tuple(num(1), num(2), num(3), num(4), num(5)))),
				Collections.singletonList("[4 5]"),
			},
			{
				opcall("SubSeq", idexp("seq"), num(6), num(5)),
				Collections.singletonList(kv("seq", tuple(num(1), num(2), num(3), num(4), num(5)))),
				Collections.singletonList("[]"),
			},
			{
				opcall("SubSeq", idexp("seq"), num(5), num(5)),
				Collections.singletonList(kv("seq", tuple(num(1), num(2), num(3), num(4), num(5)))),
				Collections.singletonList("[5]"),
			},
			{
				opcall("SubSeq", idexp("seq"), num(1), num(1)),
				Collections.singletonList(kv("seq", tuple(num(1), num(2), num(3), num(4), num(5)))),
				Collections.singletonList("[1]"),
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
			{
				opcall("Cardinality", set(num(1), num(2))),
				Collections.emptyList(),
				Collections.singletonList("2")
			},
			{
				opcall("Cardinality", set()),
				Collections.emptyList(),
				Collections.singletonList("0")
			}
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
		testCompileExpression(result, vars, compiledOutputPath -> testRunGoCode(compiledOutputPath, expected));
	}
}
