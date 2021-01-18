package pgo.trans.passes.parse.pcal;

import pgo.errors.Issue;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.tla.TLAModule;
import pgo.parser.ParsingError;
import pgo.parser.PlusCalParser;
import pgo.trans.passes.parse.ParsingIssue;

import java.nio.file.Path;

public class PlusCalParsingPass {
	private PlusCalParsingPass() {}

	public static PlusCalAlgorithm perform(Path inputFileName, CharSequence inputFileContents, TLAModule tlaModule) throws Issue {
		try {
			return PlusCalParser.readAlgorithm(inputFileName, inputFileContents, tlaModule);
		} catch (ParsingError e) {
			throw new ParsingIssue("PlusCal", e);
		}
	}
}
