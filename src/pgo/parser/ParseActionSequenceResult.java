package pgo.parser;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public class ParseActionSequenceResult extends SourceLocatable{
	SourceLocation sourceLocation;

	public ParseActionSequenceResult(SourceLocation sourceLocation) {
		this.sourceLocation = sourceLocation;
	}

	public SourceLocation getLocation() {
		return sourceLocation;
	}
	
}