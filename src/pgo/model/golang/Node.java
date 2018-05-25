package pgo.model.golang;

import java.io.IOException;
import java.io.StringWriter;

import pgo.formatters.GoNodeFormattingVisitor;
import pgo.formatters.IndentingWriter;

public abstract class Node {
	
	public abstract <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E;
	
	@Override
	public String toString() {
		StringWriter w = new StringWriter();
		IndentingWriter out = new IndentingWriter(w);
		try {
			accept(new GoNodeFormattingVisitor(out));
		} catch (IOException e) {
			throw new RuntimeException("StringWriter should not throw IOException", e);
		}
		return w.toString();
	}

}
