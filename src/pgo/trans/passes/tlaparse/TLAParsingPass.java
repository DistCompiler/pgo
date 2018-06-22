package pgo.trans.passes.tlaparse;

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
	
	public static PGoTLAModule perform(IssueContext ctx, Path filename, List<String> lines) {
		try {
			TLALexer lexer = new TLALexer(filename, lines);
			List<TLAToken> tokens = lexer.readTokens();
			List<PGoTLAModule> modules = TLAParser.readModules(tokens.listIterator());
			return modules.get(0);
		} catch (PGoTLALexerException e) {
			ctx.error(new TLALexerIssue(e));
			return null;
		} catch (TLAParseException e) {
			ctx.error(new TLAParserIssue(e.getReason()));
			return null;
		}
	}

}
