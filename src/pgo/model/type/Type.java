package pgo.model.type;

import pgo.formatters.IndentingWriter;
import pgo.formatters.TypeFormattingVisitor;
import pgo.util.Derived;
import pgo.util.DerivedVisitor;
import pgo.util.Origin;

import java.io.IOException;
import java.io.StringWriter;
import java.util.List;

public abstract class Type extends Derived {
	/**
	 * @param origins track where this type come from
	 */
	public Type(List<Origin> origins) {
		origins.forEach(this::addOrigin);
	}

	@Override
	public abstract int hashCode();

	@Override
	public abstract boolean equals(Object obj);

	@Override
	public String toString() {
		StringWriter writer = new StringWriter();
		try {
			this.accept(new TypeFormattingVisitor(new IndentingWriter(writer)));
		} catch (IOException e) {
			e.printStackTrace();
		}
		return writer.toString();
	}

	@Override
	public <T, E extends Throwable> T accept(DerivedVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	public abstract <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E;
}
