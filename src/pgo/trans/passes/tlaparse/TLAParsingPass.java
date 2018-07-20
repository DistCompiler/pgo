package pgo.trans.passes.tlaparse;

import java.nio.file.Path;
import java.util.List;

import pgo.errors.IssueContext;
import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.lexer.TLAToken;
import pgo.model.tla.PGoTLAModule;
import pgo.parser.ParseContext;
import pgo.parser.TLAParseException;
import pgo.parser.TLAParser;

public class TLAParsingPass {
	
	private TLAParsingPass() {}
	
	public static PGoTLAModule perform(IssueContext ctx, Path filename, CharSequence fileContents) {
		try {
			ParseContext parseContext = new ParseContext(filename, fileContents);
			List<PGoTLAModule> modules = TLAParser.readModules(parseContext);
			return modules.get(0);
		} catch (TLAParseException e) {
			ctx.error(new TLAParserIssue(e.getReason()));
			return null;
		}
	}

}
