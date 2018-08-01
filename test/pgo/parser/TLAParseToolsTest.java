package pgo.parser;

import org.junit.Ignore;
import org.junit.Test;
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

	private <Result extends SourceLocatable> void checkLocation(Result res, int startColumn, int endColumn, int startLine, int endLine){
		SourceLocation loc = res.getLocation();
		assertThat(Arrays.asList(loc.getStartColumn(), loc.getEndColumn(), loc.getStartLine(), loc.getEndLine()),
				is(Arrays.asList(startColumn, endColumn, startLine, endLine)));
	}

	@Test(expected = TLAParseException.class)
	public void testEmptyStringIsNotWhitespace() throws TLAParseException {
		matchWhitespace().parse(ctx(""));
	}

	@Test
	public void testOneSpaceIsWhitespace() throws TLAParseException {
		checkLocation(matchWhitespace().parse(ctx(" ")),
				1, 2, 1, 1);
	}

	@Test
	public void testMatchUnitString() throws TLAParseException {
		checkLocation(matchString("1").parse(ctx("1")),
				1, 2, 1, 1);
	}

	@Test
	public void testMatchSubString() throws TLAParseException {
		checkLocation(matchString("1").parse(ctx("12")),
				1, 2, 1, 1);
	}

	@Test(expected = TLAParseException.class)
	public void testMismatchUnitString() throws TLAParseException {
		matchString("1").parse(ctx("2"));
	}

	@Test(expected = TLAParseException.class)
	public void testEmptyStringIsNotComment() throws TLAParseException {
		matchTLAComment().parse(ctx("a"));
	}

	@Test
	public void testEmptyComment() throws TLAParseException {
		checkLocation(matchTLAComment().parse(ctx("(**)")),
				1, 5, 1, 1);
	}

	@Test
	public void testSkipTLAComments1() throws TLAParseException {
		checkLocation(
				skipWhitespaceAndTLAComments().parse(ctx("")),
				1, 1, 1, 1);
	}

	@Test
	public void testSkipTLAComments2() throws TLAParseException {
		checkLocation(
				skipWhitespaceAndTLAComments().parse(ctx("  (* (* *) (* *) *)  ")),
				1, 22, 1, 1);
	}

	@Test
	public void testMatchTLAComment1() throws TLAParseException {
		checkLocation(
				matchTLAComment().parse(ctx("(*\n" +
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
						"*)")),
				1, 3, 1, 16);
	}

	@Test
	public void testMatchTLAComment2() throws TLAParseException {
		checkLocation(matchTLAComment().parse(
				ctx("(*\n*)")),
				1, 3, 1, 2);
	}

	@Test
	public void testParseStartTranslation1() throws TLAParseException {
		checkLocation(parseStartTranslation().parse(ctx("\n" +
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
				"\\* BEGIN TRANSLATION\n")),
				1, 21, 22, 22);
	}

	@Test
	public void testParseStartTranslation2() throws TLAParseException {
		checkLocation(parseStartTranslation().parse(ctx("\n" +
						"\n" +
						"(**)\n" +
						"\\* BEGIN TRANSLATION\n")),
				1, 21, 4, 4);
	}

	@Test
	@Ignore
	public void testParseStartTranslation3() throws TLAParseException {
		checkLocation(parseStartTranslation().parse(ctx("\n" +
						"\n" +
						"\\*\n" +
						"\\* BEGIN TRANSLATION\n")),
				1, 21, 22, 22);
	}

	@Test
	public void testParseStartTranslation4() throws TLAParseException {
		checkLocation(parseStartTranslation().parse(ctx("\n" +
						"\n" +
						"\n" +
						"\\* BEGIN TRANSLATION\n")),
				1, 21, 4, 4);
	}

	@Test
	public void testRepeat1() throws TLAParseException {
		checkLocation(repeat(parseOneOf(matchString("a"), matchString("b"))).parse(ctx("abab")),
				1, 5, 1, 1);
	}

	@Test
	public void testRepeat2() throws TLAParseException {
		checkLocation(repeat(parseOneOf(parseOneOf(matchString("a"), matchString("c")), matchString("b"))).parse(ctx("acbacb")),
				1, 7, 1, 1);
	}

	@Test
	public void testRepeat3() throws TLAParseException {
		checkLocation(repeat(matchString("a")).parse(ctx("aaa")),
				1, 4, 1, 1);
	}

	@Test
	public void testParseEndTranslation() throws TLAParseException {
		checkLocation(parseEndTranslation().parse(ctx("\n" +
				"\\* END TRANSLATION\n" +
				"\n" +
				"(* If all processes are done, the counter should be equal the\n" +
				"   number of processes times the number of iterations each performed *)")),
				1, 1, 2, 3);
	}

	@Test
	public void testParseContextLineCounting() throws TLAParseException {
		LexicalContext ctx = ctx("------------------------ MODULE Euclid ----------------------------\n" +
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
				"        /\\ pc = \"a\"\n");

		checkLocation(parse4DashesOrMore().parse(ctx),
				1, 25, 1, 1);
		checkLocation(parseBuiltinToken("MODULE", -1).parse(ctx),
				26, 32, 1, 1);
		checkLocation(parseIdentifier(-1).parse(ctx),
				33, 39, 1, 1);
		checkLocation(parse4DashesOrMore().parse(ctx),
				40, 68, 1, 1);

		checkLocation(parseBuiltinToken("EXTENDS", -1).parse(ctx),
				1, 8, 2, 2);
		checkLocation(parseCommaList(parseIdentifier(-1), -1).parse(ctx),
				9, 22, 2, 2);

		checkLocation(parseBuiltinToken("CONSTANT", -1).parse(ctx),
				1, 9, 3, 3);
		checkLocation(parseIdentifier(-1).parse(ctx),
				10, 11, 3, 3);

		checkLocation(skipWhitespaceAndTLAComments().parse(ctx),
				11, 1, 3, 22);

		checkLocation(parseBuiltinToken("VARIABLES", -1).parse(ctx),
				1, 10, 22, 22);
		checkLocation(parseCommaList(parseIdentifier(-1), -1).parse(ctx),
				11, 27, 22, 22);

		checkLocation(parseIdentifier(-1).parse(ctx),
				1, 5, 24, 24);
		checkLocation(parseBuiltinToken("==", -1).parse(ctx),
				6, 8, 24, 24);
		checkLocation(parseExpression(-1).parse(ctx),
				9, 31, 24, 24);

		checkLocation(parseIdentifier(-1).parse(ctx),
				1, 5, 26, 26);
		checkLocation(parseBuiltinToken("==", -1).parse(ctx),
				6, 8, 26, 26);
		checkLocation(parseExpression(-1).parse(ctx),
				9, 20, 27, 30);
	}

}
