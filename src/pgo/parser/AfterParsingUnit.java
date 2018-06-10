package pgo.parser;

import pgo.model.tla.PGoTLAUnit;

public class AfterParsingUnit extends ActionContext {

	private PGoTLAUnit lastUnit;

	public AfterParsingUnit(PGoTLAUnit lastUnit) {
		this.lastUnit = lastUnit;
	}

	public PGoTLAUnit getLastUnit() {
		return lastUnit;
	}

	@Override
	public <T, E extends Throwable> T accept(ActionContextVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
