package pgo.trans.passes.constdef;

import java.util.HashMap;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.tla.PGoTLAExpression;
import pgo.parser.*;
import pgo.trans.passes.tlaparse.TLAParserIssue;

public class ConstantDefinitionParsingPass {
	
	private ConstantDefinitionParsingPass() {}
	
	public static Map<String, PGoTLAExpression> perform(IssueContext ctx, Map<String, Located<String>> defs){
		Map<String, PGoTLAExpression> result = new HashMap<>();
		
		for(Map.Entry<String, Located<String>> def : defs.entrySet()) {
			LexicalContext lexicalContext = new LexicalContext(
					def.getValue().getLocation().getFile(),
					def.getValue().getValue());
			try {
				PGoTLAExpression expr = TLAParser.readExpression(lexicalContext);
				result.put(def.getKey(), expr);
			} catch (TLAParseException e) {
				ctx.error(new TLAParserIssue(e.getReason()));
			}
		}
		
		return result;
	}

}
