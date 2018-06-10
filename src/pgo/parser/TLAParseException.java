package pgo.parser;

@SuppressWarnings("serial")
public class TLAParseException extends Exception {
	ParseFailure reason;

	public TLAParseException(ParseFailure reason) {
		super(reason.toString());
		this.reason = reason;
	}
	
	public ParseFailure getReason() {
		return reason;
	}

}
