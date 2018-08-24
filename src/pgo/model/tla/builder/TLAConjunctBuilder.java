package pgo.model.tla.builder;

import pgo.model.tla.*;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.function.Consumer;

public class TLAConjunctBuilder implements AutoCloseable {

	private final TLAModuleBuilder parent;
	private TLAExpression lhs;
	private final Consumer<TLAExpression> resultSink;

	public TLAConjunctBuilder(TLAModuleBuilder parent, Consumer<TLAExpression> resultSink) {
		this.lhs = null;
		this.parent = parent;
		this.resultSink = resultSink;
	}

	public TLAModuleBuilder getParent() {
		return parent;
	}

	public void addExpression(TLAExpression expr) {
		if(lhs == null) {
			lhs = expr;
		}else{
			lhs = new TLABinOp(
					SourceLocation.unknown(),
					new TLASymbol(SourceLocation.unknown(), "/\\"),
					Collections.emptyList(),
					lhs,
					expr);
		}
	}

	public TLADisjunctBuilder disjunct() {
		return new TLADisjunctBuilder(parent, this::addExpression);
	}

	public TLAIfBuilder ifexp(TLAExpression condition) {
		return new TLAIfBuilder(parent, condition, this::addExpression);
	}

	@Override
	public void close() {
		resultSink.accept(lhs != null ? lhs : new TLABool(SourceLocation.unknown(), true));
	}

	public TLAOperatorBuilder operatorDefinition(String name) {
		return parent.defineOperator(name);
	}
}
