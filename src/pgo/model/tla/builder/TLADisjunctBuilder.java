package pgo.model.tla.builder;

import pgo.model.tla.TLABinOp;
import pgo.model.tla.TLABool;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLASymbol;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.function.Consumer;

public class TLADisjunctBuilder implements AutoCloseable {

	private final TLAModuleBuilder parent;
	private final Consumer<TLAExpression> resultSink;
	private TLAExpression lhs;

	public TLADisjunctBuilder(TLAModuleBuilder parent, Consumer<TLAExpression> resultSink) {
		this.parent = parent;
		this.lhs = null;
		this.resultSink = resultSink;
	}

	public void addExpression(TLAExpression expr) {
		if(lhs == null) {
			lhs = expr;
		}else{
			lhs = new TLABinOp(
					SourceLocation.unknown(),
					new TLASymbol(SourceLocation.unknown(), "\\/"),
					Collections.emptyList(),
					lhs,
					expr);
		}
	}

	public TLADisjunctBuilder disjunct() {
		return new TLADisjunctBuilder(parent, this::addExpression);
	}

	public TLAConjunctBuilder conjunct() {
		return new TLAConjunctBuilder(parent, this::addExpression);
	}

	@Override
	public void close() {
		resultSink.accept(lhs != null ? lhs : new TLABool(SourceLocation.unknown(), true));
	}
}
