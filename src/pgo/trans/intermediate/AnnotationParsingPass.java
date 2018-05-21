package pgo.trans.intermediate;

import pgo.parser.PGoAnnotationParser;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser.ParsedPcal;

public class AnnotationParsingPass {
	
	private AnnotationParsingPass() {}
	
	public static PGoAnnotationParser perform(ParsedPcal pcal) throws PGoParseException {
		return new PGoAnnotationParser(pcal.getPGoAnnotations());
	}

}
