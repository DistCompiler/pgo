package pgo.lexer;

import static org.hamcrest.CoreMatchers.*;
import static org.junit.Assert.*;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.util.SourceLocation;

@RunWith(Parameterized.class)
public class TLALexerTest {
	
	static Path testFile = Paths.get("TEST");
	
	private static TLAToken tok(String value, TLATokenType type, int column, int line) {
		return new TLAToken(value, type, new SourceLocation(testFile, line, line, column, column+value.length()));
	}
	
	private static TLATokenType ident() {
		return TLATokenType.IDENT;
	}
	
	private static TLATokenType num() {
		return TLATokenType.NUMBER;
	}
	
	private static TLATokenType str() {
		return TLATokenType.STRING;
	}
	
	private static TLATokenType builtin() {
		return TLATokenType.BUILTIN;
	}

	@Parameters
	public static List<Object[]> data(){
		return Arrays.asList(new Object[][] {
			{ "TRUE", Collections.singletonList(tok("TRUE", builtin(), 1, 1))},
			{ "FALSE", Collections.singletonList(tok("FALSE", builtin(), 1, 1))},
			{ "a", Collections.singletonList(tok("a", ident(), 1, 1))},
			{ "a b", Arrays.asList(tok("a", ident(), 1, 1), tok("b", ident(), 3, 1)) },
			{ "  /\\ a\n  /\\ b\n  /\\ c", Arrays.asList(
					tok("/\\", builtin(), 3, 1),
					tok("a", ident(), 6, 1),
					tok("/\\", builtin(), 3, 2),
					tok("b", ident(), 6, 2),
					tok("/\\", builtin(), 3, 3),
					tok("c", ident(), 6, 3)
					)
			},
			{ ".2", Collections.singletonList(tok(".2", num(), 1, 1))},
			{ "\"abc.+#\"", Collections.singletonList(tok("abc.+#", str(), 1, 1))},
			{ "a\n\\* BEGIN TRANSLATION\nb", Arrays.asList(
					tok("a", ident(), 1, 1),
					tok("\\* BEGIN TRANSLATION", TLATokenType.BEGIN_TRANSLATION, 1, 2),
					tok("b", ident(), 1, 3)
					)
			},
			{ "a\n\\* END TRANSLATION\nb", Arrays.asList(
					tok("a", ident(), 1, 1),
					tok("\\* END TRANSLATION", TLATokenType.END_TRANSLATION, 1, 2),
					tok("b", ident(), 1, 3)
					)
			},
			{ "a\n\\* BEGIN TRNSLATION\nb", Arrays.asList(
					tok("a", ident(), 1, 1),
					tok("b", ident(), 1, 3)
					)
			},
			{ "a\n\\* END TRANSLATION \nb", Arrays.asList(
					tok("a", ident(), 1, 1),
					tok("b", ident(), 1, 3)
					)
			},
			{ "<=", Collections.singletonList(tok("<=", builtin(), 1, 1))},
			{ "\\** BEGIN TRANSLATION", Collections.singletonList(tok("\\** BEGIN TRANSLATION", TLATokenType.BEGIN_TRANSLATION, 1, 1))},
			{ "\\notin", Collections.singletonList(tok("\\notin", builtin(), 1, 1))},
			{ "CONSTANT procs (* @PGo{ arg int }@PGo *), iters (* @PGo{ arg int }@PGo *)",
					Arrays.asList(
							tok("CONSTANT", builtin(), 1, 1),
							tok("procs", ident(), 10, 1),
							tok(",", builtin(), 41, 1),
							tok("iters", ident(), 43, 1))},
		});
	}

	String input;
	List<TLAToken> expected;
	
	public TLALexerTest(String input, List<TLAToken> expected) {
		this.input = input;
		this.expected = expected;
	}
	
	@Test
	public void test() throws PGoTLALexerException {
		TLALexer lexer = new TLALexer(testFile, 1, 1, Arrays.asList(input.split("\n")));
		// don't ignore the expression because it's not in a module
		lexer.requireModule(false);
		
		List<TLAToken> tokens = lexer.readTokens();
		
		assertThat(tokens, is(expected));
	}
}
