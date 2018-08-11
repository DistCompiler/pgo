package pgo.trans.passes.constdef;

import java.util.HashMap;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.tla.TLAExpression;
import pgo.parser.*;
import pgo.trans.passes.tlaparse.ParsingIssue;

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
