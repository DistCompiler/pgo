package pgo.model.tla.builder;

import pgo.model.tla.*;
import pgo.util.NameCleaner;
import pgo.util.SourceLocation;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;

public class TLAOperatorBuilder implements AutoCloseable {

	private final TLAModuleBuilder parent;
	private final NameCleaner nameCleaner;
	private final String name;
	private final Consumer<TLAOperatorDefinition> resultSink;
	private TLAExpression body;
	private final List<TLAOpDecl> arguments;

	public TLAOperatorBuilder(TLAModuleBuilder parent, NameCleaner nameCleaner, String name, Consumer<TLAOperatorDefinition> resultSink) {
		this.parent = parent;
		this.nameCleaner = nameCleaner.child();
		this.name = name;
		this.resultSink = resultSink;
		this.arguments = new ArrayList<>();
	}

	public TLAConjunctBuilder getConjunctBuilder() {
		return new TLAConjunctBuilder(parent, b -> body = b);
	}

	public String addArgument(String name) {
		String actualName = nameCleaner.cleanName(name);
		arguments.add(TLAOpDecl.Id(SourceLocation.unknown(), new TLAIdentifier(SourceLocation.unknown(), actualName)));
		return actualName;
	}

	@Override
	public void close() {
		resultSink.accept(new TLAOperatorDefinition(
				SourceLocation.unknown(),
				new TLAIdentifier(SourceLocation.unknown(), name),
				arguments,
				body,
				false));
	}
}
