package pgo.model.pcal;

import pgo.util.SourceLocation;

public class Skip extends Statement {

	public Skip(SourceLocation location) {
		super(location);
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		return 0;
	}

	@Override
	public boolean equals(Object obj) {
		return obj != null && obj instanceof Skip;
	}

}
