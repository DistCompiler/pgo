package pgo.model.tla.builder;

import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAIf;
import pgo.util.SourceLocation;

import java.util.function.Consumer;

public class TLAIfBuilder implements AutoCloseable {
	private final TLAModuleBuilder parent;
	private final TLAExpression condition;
	private final Consumer<TLAExpression> resultSink;
	private TLAExpression whenTrue;
	private TLAExpression whenFalse;

	public TLAIfBuilder(TLAModuleBuilder parent, TLAExpression condition, Consumer<TLAExpression> resultSink) {
		this.parent = parent;
		this.condition = condition;
		this.resultSink = resultSink;
		this.whenTrue = null;
		this.whenFalse = null;
	}

	public TLAConjunctBuilder getWhenTrueBuilder() {
		return new TLAConjunctBuilder(parent, result -> whenTrue = result);
	}

	public TLAConjunctBuilder getWhenFalseBuilder() {
		return new TLAConjunctBuilder(parent, result -> whenFalse = result);
	}

	@Override
	public void close() {
		resultSink.accept(new TLAIf(SourceLocation.unknown(), condition, whenTrue, whenFalse));
	}
}
