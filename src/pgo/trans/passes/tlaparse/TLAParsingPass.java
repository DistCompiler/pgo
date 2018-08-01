package pgo.trans.passes.tlaparse;

import java.nio.file.Path;
import java.util.List;

import pgo.errors.IssueContext;
import pgo.model.tla.PGoTLAModule;
import pgo.parser.LexicalContext;
import pgo.parser.TLAParseException;
import pgo.parser.TLAParser;

public class TLAParsingPass {
	
	private TLAParsingPass() {}
	
	public static PGoTLAModule perform(IssueContext ctx, Path filename, CharSequence fileContents) {
		try {
			LexicalContext lexicalContext = new LexicalContext(filename, fileContents);
			List<PGoTLAModule> modules = TLAParser.readModules(lexicalContext);
			return modules.get(0);
		} catch (TLAParseException e) {
			ctx.error(new TLAParserIssue(e.getReason()));
			return null;
		}
	}

}
