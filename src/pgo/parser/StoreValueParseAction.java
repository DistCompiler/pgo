package pgo.parser;

public class StoreValueParseAction extends ParseAction {
	private int source;
	private int destination;
	private Variable destVariable;

	public StoreValueParseAction(int source, int destination, Variable destVariable) {
		this.source = source;
		this.destination = destination;
		this.destVariable = destVariable;
	}

	public int getSource() { return source; }
	public int getDestination() { return destination; }
	public Variable getDestVariable() { return destVariable; }

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
