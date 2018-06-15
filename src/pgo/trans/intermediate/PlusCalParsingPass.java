package pgo.trans.intermediate;

import pcal.AST;
import pgo.errors.IssueContext;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser;

import java.util.List;

public class PlusCalParsingPass {
	private PlusCalParsingPass() {}

	public static AST perform(IssueContext ctx, List<String> lines) {
		try {
			return PcalParser.parse(lines);
		} catch (PGoParseException e) {
			ctx.error(new PlusCalParserIssue(e.getMessage()));
			return null;
		}
	}
}
