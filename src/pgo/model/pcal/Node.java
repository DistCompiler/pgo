package pgo.model.pcal;

import java.io.IOException;
import java.io.StringWriter;

import pgo.formatters.IndentingWriter;
import pgo.formatters.NodeFormattingVisitor;
import pgo.scope.UID;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public abstract class Node extends SourceLocatable {
	
	private SourceLocation location;
	private UID uid;
	
	public Node(SourceLocation location) {
		this.location = location;
		this.uid = new UID();
		this.uid.addOrigin(this);
	}
	
	public abstract Node copy();

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
	
	public abstract <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E;
	
	@Override
	public String toString() {
		StringWriter w = new StringWriter();
		IndentingWriter out = new IndentingWriter(w);
		try {
			accept(new NodeFormattingVisitor(out));
		} catch (IOException e) {
			throw new RuntimeException("unreachable", e);
		}
		return w.toString();
	}

}
