package pgo.trans.passes.constdef;

import pgo.errors.IssueContext;
import pgo.model.tla.TLAExpression;
import pgo.parser.LexicalContext;
import pgo.parser.Located;
import pgo.parser.ParseFailureException;
import pgo.parser.TLAParser;
import pgo.trans.passes.tlaparse.ParsingIssue;

import java.util.HashMap;
import java.util.Map;

public class ConstantDefinitionParsingPass {
	
	private ConstantDefinitionParsingPass() {}
	
	public static Map<String, TLAExpression> perform(IssueContext ctx, Map<String, Located<String>> defs){
		Map<String, TLAExpression> result = new HashMap<>();
		
		for(Map.Entry<String, Located<String>> def : defs.entrySet()) {
			LexicalContext lexicalContext = new LexicalContext(
					def.getValue().getLocation().getFile(),
					def.getValue().getValue());
			try {
				TLAExpression expr = TLAParser.readExpression(lexicalContext);
				result.put(def.getKey(), expr);
			} catch (ParseFailureException e) {
				ctx.error(new ParsingIssue("TLA+ constant", e.getReason()));
			}
		}
		
		return result;
	}

}
