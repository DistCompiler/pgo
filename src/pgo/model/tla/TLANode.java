package pgo.model.tla;

import pgo.formatters.IndentingWriter;
import pgo.formatters.TLANodeFormattingVisitor;
import pgo.scope.UID;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.io.IOException;
import java.io.StringWriter;

/**
 * 
 * The base class for any TLA AST node. Usually too vague to be useful,
 * but can be useful in error reporting as it defines every TLA AST node
 * as knowing their source file location.
 *
 */
public abstract class TLANode extends SourceLocatable {
	private final SourceLocation location;
	private final UID uid;
	
	public TLANode(SourceLocation location) {
		this.location = location;
		this.uid = new UID();
		this.uid.addOrigin(this);
	}
	
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
	
	@Override
	public String toString() {
		StringWriter out = new StringWriter();
		try {
			accept(new TLANodeFormattingVisitor(new IndentingWriter(out)));
		} catch (IOException e) {
			RuntimeException ex = new RuntimeException("You should never get an IO error from a StringWriter", e);
			throw ex;
		}
		return out.toString();
	}
	
	public abstract TLANode copy();
	
	public abstract <T, E extends Throwable> T accept(TLANodeVisitor<T, E> v) throws E;
	
}
