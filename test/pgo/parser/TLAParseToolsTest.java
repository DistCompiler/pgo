package pgo.parser;

import org.junit.Ignore;
import org.junit.Test;
import pgo.model.tla.TLAExpression;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

import static pgo.parser.ParseTools.*;
import static pgo.parser.TLAParser.*;

public class TLAParseToolsTest {

	static Path testFile = Paths.get("TEST");

	private LexicalContext ctx(String contents){
		return new LexicalContext(testFile, String.join(System.lineSeparator(), contents.split("\n")));
	}

	private <Result extends SourceLocatable> Result executeGrammar(Grammar<Result> grammar, LexicalContext ctx) throws ParseFailureException {
		Grammar<Result> nested = emptySequence()
				.dependentPart(grammar, ignore -> new VariableMap().put(MIN_COLUMN, -1))
				.map(seq -> seq.getValue().getFirst());

		return nested.parse(ctx);
	}

	private <Result extends SourceLocatable> void checkLocation(Grammar<Result> grammar, LexicalContext ctx, int startColumn, int endColumn, int startLine, int endLine) throws ParseFailureException {
		Result res = executeGrammar(grammar, ctx);
		
		SourceLocation loc = res.getLocation();
		assertThat(Arrays.asList(loc.getStartColumn(), loc.getEndColumn(), loc.getStartLine(), loc.getEndLine()),
				is(Arrays.asList(startColumn, endColumn, startLine, endLine)));
	}

	@Test(expected = ParseFailureException.class)
	public void testEmptyStringIsNotWhitespace() throws ParseFailureException {
		executeGrammar(matchWhitespace(), ctx(""));
	}

	@Test
	public void testOneSpaceIsWhitespace() throws ParseFailureException {
		checkLocation(matchWhitespace(), ctx(" "),
				1, 2, 1, 1);
	}

	@Test
	public void testMatchUnitString() throws ParseFailureException {
		checkLocation(matchString("1"), ctx("1"),
				1, 2, 1, 1);
	}

	@Test
	public void testMatchSubString() throws ParseFailureException {
		checkLocation(matchString("1"), ctx("12"),
				1, 2, 1, 1);
	}

	@Test(expected = ParseFailureException.class)
	public void testMismatchUnitString() throws ParseFailureException {
		executeGrammar(matchString("1"), ctx("2"));
	}

	@Test(expected = ParseFailureException.class)
	public void testEmptyStringIsNotComment() throws ParseFailureException {
		executeGrammar(matchTLAComment(), ctx("a"));
	}

	@Test
	public void testEmptyComment() throws ParseFailureException {
		checkLocation(matchTLAComment(), ctx("(**)"),
				1, 5, 1, 1);
	}

	@Test
	public void testSkipTLAComments1() throws ParseFailureException {
		checkLocation(
				skipWhitespaceAndTLAComments(), ctx(""),
				1, 1, 1, 1);
	}

	@Test
	public void testSkipTLAComments2() throws ParseFailureException {
		checkLocation(
				skipWhitespaceAndTLAComments(), ctx("  (* (* *) (* *) *)  "),
				1, 22, 1, 1);
	}

	@Test
	public void testMatchTLAComment1() throws ParseFailureException {
		checkLocation(
				matchTLAComment(), ctx("(*\n" +
						"--algorithm Euclid {    \\** @PGo{ arg N int }@PGo\n" +
						"  variables u = 24;\n" +
						"            v \\in 1 .. N; \n" +
						"            v_init = v;\n" +
						"  {\n" +
						"  a:  while (u # 0) {\n" +
						"      if (u < v) {\n" +
						"          u := v || v := u;\n" +
						"      };\n" +
						"  b:    u := u - v;\n" +
						"    };\n" +
						"    print <<24, v_init, \"have gcd\", v>>\n" +
						"  }\n" +
						"}\n" +
						"*)"),
				1, 3, 1, 16);
	}

	@Test
	public void testMatchTLAComment2() throws ParseFailureException {
		checkLocation(matchTLAComment(),
				ctx("(*\n*)"),
				1, 3, 1, 2);
	}

	@Test
	public void testParseStartTranslation1() throws ParseFailureException {
		checkLocation(parseStartTranslation(), ctx("\n" +
				"\n" +
				"(*\n" +
				"\n" +
				"--algorithm counter {\n" +
				"  (** @PGo{ arg procs int }@PGo\n" +
				"      @PGo{ arg iters int }@PGo\n" +
				"   **)\n" +
				"  variables counter = 0;\n" +
				"\n" +
				"  fair process (P \\in 0..procs-1)\n" +
				"  variables i = 0;\n" +
				"  {\n" +
				"      w: while (i < iters) {\n" +
				"          incCounter: counter := counter + 1;\n" +
				"                      print counter;\n" +
				"          nextIter:   i := i + 1;\n" +
				"      }\n" +
				"  }\n" +
				"}\n" +
				"*)\n" +
				"\\* BEGIN TRANSLATION\n"),
				1, 21, 22, 22);
	}

	@Test
	public void testParseStartTranslation2() throws ParseFailureException {
		checkLocation(parseStartTranslation(), ctx("\n" +
						"\n" +
						"(**)\n" +
						"\\* BEGIN TRANSLATION\n"),
				1, 21, 4, 4);
	}

	@Test
	@Ignore
	public void testParseStartTranslation3() throws ParseFailureException {
		checkLocation(parseStartTranslation(), ctx("\n" +
						"\n" +
						"\\*\n" +
						"\\* BEGIN TRANSLATION\n"),
				1, 21, 22, 22);
	}

	@Test
	public void testParseStartTranslation4() throws ParseFailureException {
		checkLocation(parseStartTranslation(), ctx("\n" +
						"\n" +
						"\n" +
						"\\* BEGIN TRANSLATION\n"),
				1, 21, 4, 4);
	}

	@Test
	public void testRepeat1() throws ParseFailureException {
		checkLocation(repeat(parseOneOf(matchString("a"), matchString("b"))), ctx("abab"),
				1, 5, 1, 1);
	}

	@Test
	public void testRepeat2() throws ParseFailureException {
		checkLocation(repeat(parseOneOf(parseOneOf(matchString("a"), matchString("c")), matchString("b"))), ctx("acbacb"),
				1, 7, 1, 1);
	}

	@Test
	public void testRepeat3() throws ParseFailureException {
		checkLocation(repeat(matchString("a")), ctx("aaa"),
				1, 4, 1, 1);
	}

	@Test
	public void testParseEndTranslation() throws ParseFailureException {
		checkLocation(parseEndTranslation(), ctx("\n" +
				"\\* END TRANSLATION\n" +
				"\n" +
				"(* If all processes are done, the counter should be equal the\n" +
				"   number of processes times the number of iterations each performed *)"),
				1, 1, 2, 3);
	}

	@Test
	public void testParseIdentifier() throws ParseFailureException {
		checkLocation(parseTLAIdentifier(), ctx(" Euclid"),
				2, 8, 1, 1);
	}

	@Test(expected = ParseFailureException.class)
	public void testMatchTLAIdentifierRejectReservedWords() throws ParseFailureException {
		executeGrammar(parseTLAIdentifier(), ctx("OTHER"));
	}

	@Test(expected = ParseFailureException.class)
	public void testRejectString1() throws ParseFailureException {
		executeGrammar(reject(matchString("a")), ctx("a"));
	}

	@Test
	public void testRejectString2() throws ParseFailureException {
		checkLocation(
				emptySequence()
						.drop(reject(matchString("b")))
						.drop(matchString("a")),
				ctx("a"),
				1, 2, 1, 1);
	}

	@Test
	public void testChoice1() throws ParseFailureException {
		checkLocation(
				parseOneOf(matchString("a"), matchString("b")),
				ctx("a"),
				1, 2, 1, 1);
	}

	@Test
	public void testChoice2() throws ParseFailureException {
		checkLocation(
				parseOneOf(matchString("a"), matchString("b")),
				ctx("b"),
				1, 2, 1, 1);
	}

	@Test
	public void testChoice3() throws ParseFailureException {
		checkLocation(
				emptySequence()
						.drop(matchString("a"))
						.drop(parseOneOf(
								matchString("a"),
								matchString("b")
						))
						.drop(matchString("c")),
				ctx("abc"),
				1, 4, 1, 1);
	}

	@Test
	public void testChoice4() throws ParseFailureException {
		checkLocation(
				emptySequence()
						.drop(matchString("a"))
						.drop(parseOneOf(
								matchString("bc"),
								matchString("b")
						).map(v -> v))
						.drop(matchString("c")),
				ctx("abc"),
				1, 4, 1, 1);
	}

	@Test
	public void testChoice5() throws ParseFailureException {
		checkLocation(
				parseFairnessConstraint(),
				ctx("WF_foo(bar)"),
				1, 12, 1, 1);
	}

	@Test
	public void testChoice6() throws ParseFailureException {
		checkLocation(
				emptySequence()
						.drop(parseOneOf(matchString("a"), matchString("b")))
						.drop(parseOneOf(matchString("bc"), matchString("b")))
						.drop(matchString("c")),
				ctx("abc"),
				1, 4, 1, 1);
	}

	@Test
	public void testParseGeneralIdentifier() throws ParseFailureException {
		checkLocation(parseGeneralIdentifier(), ctx("a(1,2)!b"),
				1, 9, 1, 1);
	}

	@Test
	public void testSkipTLAWhitespaceAndComments() throws ParseFailureException {
		checkLocation(skipWhitespaceAndTLAComments(), ctx("\n" +
				"\n" +
				"(*\n" +
				"--algorithm Euclid {    \\** @PGo{ arg N int }@PGo\n" +
				"  variables u = 24;\n" +
				"            v \\in 1 .. N; \n" +
				"            v_init = v;\n" +
				"  {\n" +
				"  a:  while (u # 0) {\n" +
				"      if (u < v) {\n" +
				"          u := v || v := u;\n" +
				"      };\n" +
				"  b:    u := u - v;\n" +
				"    };\n" +
				"    print <<24, v_init, \"have gcd\", v>>\n" +
				"  }\n" +
				"}\n" +
				"*)\n" +
				"\\* BEGIN TRANSLATION\n" +
				"VARIABLES"),
				1, 1, 1, 20);
	}

	@Test
	public void testRelativeOperatorPrecedence1() throws ParseFailureException {
		checkLocation(OPERATORS_BY_PRECEDENCE.get(4), ctx("2 /\\ 3"),
				1, 2, 1, 1);
	}

	@Test
	public void testRelativeOperatorPrecedence2() throws ParseFailureException {
		checkLocation(OPERATORS_BY_PRECEDENCE.get(4), ctx("[] 2 /\\ 3"),
				1, 5, 1, 1);
	}

	@Test
	public void testRelativeOperatorPrecedence3() throws ParseFailureException {
		checkLocation(OPERATORS_BY_PRECEDENCE.get(16), ctx("2 /\\ 3"),
				1, 2, 1, 1);
	}

	@Test
	public void testParseContextLineCounting() throws ParseFailureException {
		String theString = "------------------------ MODULE Euclid ----------------------------\n" +
				"EXTENDS Naturals, TLC\n" +
				"CONSTANT N\n" +
				"\n" +
				"(*\n" +
				"--algorithm Euclid {    \\** @PGo{ arg N int }@PGo\n" +
				"  variables u = 24;\n" +
				"            v \\in 1 .. N; \n" +
				"            v_init = v;\n" +
				"  {\n" +
				"  a:  while (u # 0) {\n" +
				"      if (u < v) {\n" +
				"          u := v || v := u;\n" +
				"      };\n" +
				"  b:    u := u - v;\n" +
				"    };\n" +
				"    print <<24, v_init, \"have gcd\", v>>\n" +
				"  }\n" +
				"}\n" +
				"*)\n" +
				"\\* BEGIN TRANSLATION\n" +
				"VARIABLES u, v, v_init, pc\n" +
				"\n" +
				"vars == << u, v, v_init, pc >>\n" +
				"\n" +
				"Init == (* Global variables *)\n" +
				"        /\\ u = 24\n" +
				"        /\\ v \\in 1 .. N\n" +
				"        /\\ v_init = v\n" +
				"        /\\ pc = \"a\"\n";
		LexicalContext ctx = ctx(theString);

		System.out.println(theString);

		checkLocation(parse4DashesOrMore(), ctx,
				1, 25, 1, 1);
		checkLocation(parseTLAToken("MODULE"), ctx,
				26, 32, 1, 1);
		checkLocation(parseTLAIdentifier(), ctx,
				33, 39, 1, 1);
		checkLocation(parse4DashesOrMore(), ctx,
				40, 68, 1, 1);

		checkLocation(parseTLAToken("EXTENDS"), ctx,
				1, 8, 2, 2);
		checkLocation(parseCommaList(parseTLAIdentifier()), ctx,
				9, 22, 2, 2);

		checkLocation(parseTLAToken("CONSTANT"), ctx,
				1, 9, 3, 3);
		checkLocation(parseTLAIdentifier(), ctx,
				10, 11, 3, 3);

		checkLocation(skipWhitespaceAndTLAComments(), ctx,
				11, 1, 3, 22);

		checkLocation(parseTLAToken("VARIABLES"), ctx,
				1, 10, 22, 22);
		checkLocation(parseCommaList(parseTLAIdentifier()), ctx,
				11, 27, 22, 22);

		checkLocation(parseTLAIdentifier(), ctx,
				1, 5, 24, 24);
		checkLocation(parseTLAToken("=="), ctx,
				6, 8, 24, 24);
		checkLocation(parseExpression(), ctx,
				9, 31, 24, 24);

		checkLocation(parseTLAIdentifier(), ctx,
				1, 5, 26, 26);
		checkLocation(parseTLAToken("=="), ctx,
				6, 8, 26, 26);
		checkLocation(parseExpression(), ctx,
				9, 20, 27, 30);
	}

}
