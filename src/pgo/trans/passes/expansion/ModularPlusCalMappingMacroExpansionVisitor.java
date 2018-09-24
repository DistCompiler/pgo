package pgo.trans.passes.expansion;

import pgo.TODO;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;

import java.util.List;
import java.util.Map;

public class ModularPlusCalMappingMacroExpansionVisitor
		extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	private final IssueContext ctx;
	private final Map<String, PlusCalVariableDeclaration> arguments;
	private final Map<String, TLAExpression> boundArguments;
	private final Map<String, ModularPlusCalMappingMacro> mappingMacros;
	private final Map<String, List<String>> mappings;

	public ModularPlusCalMappingMacroExpansionVisitor(IssueContext ctx,
	                                                  Map<String, PlusCalVariableDeclaration> arguments,
	                                                  Map<String, TLAExpression> boundArguments,
	                                                  Map<String, ModularPlusCalMappingMacro> mappingMacros,
	                                                  Map<String, List<String>> mappings) {
		this.ctx = ctx;
		this.arguments = arguments;
		this.boundArguments = boundArguments;
		this.mappingMacros = mappingMacros;
		this.mappings = mappings;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalSkip skip) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith with) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new TODO();
	}
}
