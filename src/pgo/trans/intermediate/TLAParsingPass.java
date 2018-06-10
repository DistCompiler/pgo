package pgo.trans.intermediate;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import pgo.errors.IssueContext;
import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.lexer.TLAToken;
import pgo.model.tla.PGoTLAModule;
import pgo.parser.TLAParseException;
import pgo.parser.TLAParser;

public class TLAParsingPass {
	
	private TLAParsingPass() {}
	
	public static PGoTLAModule perform(IssueContext ctx, Path filename) {
		try {
			TLALexer lexer = new TLALexer(filename);
			List<TLAToken> tokens = lexer.readTokens();
			List<PGoTLAModule> modules = TLAParser.readModules(tokens.listIterator());
			return modules.get(0);
		} catch (IOException e) {
			ctx.error(new IOErrorIssue(e));
			return null;
		} catch (PGoTLALexerException e) {
			ctx.error(new TLALexerIssue(e));
			return null;
		} catch (TLAParseException e) {
			ctx.error(new TLAParserIssue(e.getReason()));
			return null;
		}
	}

}
