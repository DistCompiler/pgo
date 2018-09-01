package pgo.model.mpcal;

import pgo.Unreachable;
import pgo.formatters.IndentingWriter;
import pgo.scope.UID;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.io.IOException;
import java.io.StringWriter;

public abstract class ModularPlusCalNode extends SourceLocatable {

	private SourceLocation location;
	private UID uid;

	public ModularPlusCalNode(SourceLocation location) {
		this.location = location;
		this.uid = new UID();
		this.uid.addOrigin(this);
	}

	public abstract ModularPlusCalNode copy();

	@Override
	public SourceLocation getLocation() {
		return location;
	}

	public UID getUID() {
		return uid;
	}

	@Override
	public abstract int hashCode();

	@Override
	public abstract boolean equals(Object obj);

	public abstract <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E;

	@Override
	public String toString() {
		StringWriter w = new StringWriter();
		IndentingWriter out = new IndentingWriter(w);
		try {
			accept(new ModularPlusCalNodeFormattingVisitor(out));
		} catch (IOException e) {
			throw new Unreachable(e);
		}
		return w.toString();
	}

}
