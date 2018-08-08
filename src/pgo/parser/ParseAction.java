package pgo.parser;

public abstract class ParseAction {

	public abstract boolean isDecidable();

	public abstract boolean accept(ParseActionExecutor exec);

}
