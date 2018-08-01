package pgo.parser;

import pgo.util.SourceLocation;

import java.util.NavigableMap;
import java.util.Set;

@SuppressWarnings("serial")
public class TLAParseException extends Exception {
	private NavigableMap<SourceLocation, Set<ParseFailure>> reason;

	public TLAParseException( NavigableMap<SourceLocation, Set<ParseFailure>> reason) {
		super(reason.lastEntry().getValue().toString());
		this.reason = reason;
	}
	
	public NavigableMap<SourceLocation, Set<ParseFailure>> getReason() {
		return reason;
	}

}
