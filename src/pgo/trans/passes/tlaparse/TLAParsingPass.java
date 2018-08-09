package pgo.trans.passes.tlaparse;

import java.nio.file.Path;
import java.util.List;

import pgo.errors.IssueContext;
import pgo.model.tla.TLAModule;
import pgo.parser.LexicalContext;
import pgo.parser.ParseFailureException;
import pgo.parser.TLAParser;

public class TLAParsingPass {
	
	private TLAParsingPass() {}
	
	public static TLAModule perform(IssueContext ctx, Path filename, CharSequence fileContents) {
		try {
			LexicalContext lexicalContext = new LexicalContext(filename, fileContents);
			List<TLAModule> modules = TLAParser.readModules(lexicalContext);
			return modules.get(0);
		} catch (ParseFailureException e) {
			ctx.error(new TLAParserIssue(e.getReason()));
			return null;
		}
	}

}
