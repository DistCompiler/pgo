package pgo.trans.passes.constdef;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.lexer.PGoTLALexerException;
import pgo.lexer.TLALexer;
import pgo.lexer.TLAToken;
import pgo.model.tla.PGoTLAExpression;
import pgo.parser.LocatedString;
import pgo.parser.ParseContext;
import pgo.parser.TLAParseException;
import pgo.parser.TLAParser;
import pgo.trans.passes.tlaparse.TLALexerIssue;
import pgo.trans.passes.tlaparse.TLAParserIssue;

public class ConstantDefinitionParsingPass {
	
	private ConstantDefinitionParsingPass() {}
	
	public static Map<String, PGoTLAExpression> perform(IssueContext ctx, Map<String, LocatedString> defs){
		Map<String, PGoTLAExpression> result = new HashMap<>();
		
		for(Map.Entry<String, LocatedString> def : defs.entrySet()) {
			ParseContext parseContext = new ParseContext(
					def.getValue().getLocation().getFile(),
					def.getValue().getValue());
			try {
				PGoTLAExpression expr = TLAParser.readExpression(parseContext);
				result.put(def.getKey(), expr);
			} catch (TLAParseException e) {
				ctx.error(new TLAParserIssue(e.getReason()));
			}
		}
		
		return result;
	}

}
