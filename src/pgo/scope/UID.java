package pgo.scope;

import pgo.util.Derived;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

public class UID extends Derived {
	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public String toString() {
		StringBuilder b = new StringBuilder(super.toString());
		b.append("(from ");
		boolean first = true;
		for(Origin o : this.getOrigins()) {
			if(first) {
				first = false;
			}else {
				b.append(", ");
			}
			b.append(o);
		}
		b.append(")");
		return b.toString();
	}
}
