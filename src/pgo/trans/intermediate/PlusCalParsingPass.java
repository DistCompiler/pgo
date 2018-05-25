package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser;

import java.nio.file.Path;

public class PlusCalParsingPass {
	private PlusCalParsingPass() {}

	public static PcalParser.ParsedPcal perform(IssueContext ctx, Path filename) {
		PcalParser parser = new PcalParser(filename);
		try {
			return parser.parse();
		} catch (PGoParseException e) {
			ctx.error(new PlusCalParserIssue(e.getMessage()));
			return null;
		}
	}
}
