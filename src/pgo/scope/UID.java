package pgo.scope;

import pgo.util.Derived;
import pgo.util.DerivedVisitor;

public class UID extends Derived {

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
