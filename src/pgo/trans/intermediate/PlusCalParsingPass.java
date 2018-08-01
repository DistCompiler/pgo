package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.model.pcal.Algorithm;
import pgo.parser.*;
import pgo.trans.passes.tlaparse.TLAParserIssue;

import java.nio.file.Path;

public class PlusCalParsingPass {
	private PlusCalParsingPass() {}

	public static Algorithm perform(IssueContext ctx, Path inputFileName, CharSequence inputFileContents) {
		try {
			return PcalParser.readAlgorithm(new LexicalContext(inputFileName, inputFileContents));
		} catch (TLAParseException e) {
			ctx.error(new TLAParserIssue(e.getReason()));
			return null;
		}
	}
}
