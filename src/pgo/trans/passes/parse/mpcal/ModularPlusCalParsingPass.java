package pgo.trans.passes.parse.mpcal;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.parser.LexicalContext;
import pgo.parser.ParseFailureException;
import pgo.parser.ModularPlusCalParser;
import pgo.trans.passes.parse.tla.ParsingIssue;

import java.nio.file.Path;

public class ModularPlusCalParsingPass {
	private ModularPlusCalParsingPass() {}

	public static boolean hasModularPlusCalBlock(Path inputFileName, CharSequence inputFileContents) {
		return ModularPlusCalParser.hasModularPlusCalBlock(new LexicalContext(inputFileName, inputFileContents));
	}

	public static ModularPlusCalBlock perform(IssueContext ctx, Path inputFileName, CharSequence inputFileContents) {
		try {
			return ModularPlusCalParser.readBlock(new LexicalContext(inputFileName, inputFileContents));
		} catch (ParseFailureException e) {
			ctx.error(new ParsingIssue("ModularPlusCal", e.getReason()));
			return null;
		}
	}
}
