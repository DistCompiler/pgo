package pgo.model.mpcal;

import pgo.TODO;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalStatementVisitor;
import pgo.util.SourceLocation;

/**
 * Read statement
 *
 * read exp;
 *
 * where exp may contain $value
 */
public class ModularPlusCalRead extends PlusCalStatement {
	public ModularPlusCalRead(SourceLocation location) {
		super(location);
	}

	@Override
	public PlusCalStatement copy() {
		throw new TODO();
	}

	@Override
	public int hashCode() {
		throw new TODO();
	}

	@Override
	public boolean equals(Object obj) {
		throw new TODO();
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
