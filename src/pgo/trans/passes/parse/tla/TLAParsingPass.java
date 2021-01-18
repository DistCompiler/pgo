package pgo.trans.passes.parse.tla;

import pgo.errors.Issue;
import pgo.model.tla.TLAModule;
import pgo.parser.ParsingError;
import pgo.parser.TLAParser;
import pgo.trans.passes.parse.ParsingIssue;

import java.nio.file.Path;

public class TLAParsingPass {
    private TLAParsingPass() {}

    public static TLAModule perform(Path inputFileName, CharSequence inputFileContents) throws Issue {
        try {
            return TLAParser.readModuleBeforeTranslation(inputFileName, inputFileContents);
        } catch (ParsingError e) {
            throw new ParsingIssue("TLA+", e);
        }
    }
}
