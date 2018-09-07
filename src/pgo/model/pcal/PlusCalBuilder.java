package pgo.model.pcal;

import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAUnit;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.Arrays;
import java.util.List;

public class PlusCalBuilder {
	private PlusCalBuilder() {}

	public static PlusCalDefaultInitValue PLUSCAL_DEFAULT_INIT_VALUE = new PlusCalDefaultInitValue(SourceLocation.unknown());

	public static PlusCalAlgorithm algorithm(String name, List<PlusCalVariableDeclaration> vars, List<ModularPlusCalArchetype> archetypes, List<PlusCalMacro> macros, List<PlusCalProcedure> procedures, List<TLAUnit> units, PlusCalLabeledStatements... statements) {
		return new PlusCalAlgorithm(SourceLocation.unknown(), PlusCalFairness.UNFAIR,
				new Located<>(SourceLocation.unknown(), name), vars, macros, procedures, units,
				new PlusCalSingleProcess(SourceLocation.unknown(), Arrays.asList(statements)));
	}

	public static PlusCalAlgorithm algorithm(String name, List<PlusCalVariableDeclaration> vars, List<ModularPlusCalArchetype> archetypes, List<PlusCalMacro> macros, List<PlusCalProcedure> procedures, List<TLAUnit> units, PlusCalProcess... processes) {
		return new PlusCalAlgorithm(SourceLocation.unknown(), PlusCalFairness.UNFAIR,
				new Located<>(SourceLocation.unknown(), name), vars, macros, procedures, units,
				new PlusCalMultiProcess(SourceLocation.unknown(), Arrays.asList(processes)));
	}

	public static PlusCalVariableDeclaration pcalVarDecl(String name, boolean isSet, TLAExpression value) {
		return new PlusCalVariableDeclaration(
				SourceLocation.unknown(), new Located<>(SourceLocation.unknown(), name), isSet, value);
	}

	public static PlusCalMacro macro(String name, List<String> args, PlusCalStatement... statements) {
		return new PlusCalMacro(SourceLocation.unknown(), name, args, Arrays.asList(statements));
	}

	public static PlusCalProcedure procedure(String name, List<PlusCalVariableDeclaration> args,
	                                         List<PlusCalVariableDeclaration> vars, PlusCalStatement... statements) {
		return new PlusCalProcedure(SourceLocation.unknown(), name, args, vars, Arrays.asList(statements));
	}

	public static PlusCalProcess process(PlusCalVariableDeclaration name, PlusCalFairness fairness,
	                                     List<PlusCalVariableDeclaration> vars, PlusCalStatement... statements) {
		return new PlusCalProcess(SourceLocation.unknown(), name, fairness, vars, Arrays.asList(statements));
	}

	public static PlusCalLabel label(String name) {
		return new PlusCalLabel(SourceLocation.unknown(), name, PlusCalLabel.Modifier.NONE);
	}

	public static PlusCalLabeledStatements labeled(PlusCalLabel label, PlusCalStatement... statements) {
		return new PlusCalLabeledStatements(SourceLocation.unknown(), label, Arrays.asList(statements));
	}

	public static PlusCalMacroCall macroCall(String name, TLAExpression... args) {
		return new PlusCalMacroCall(SourceLocation.unknown(), name, Arrays.asList(args));
	}

	public static PlusCalPrint printS(TLAExpression expr) {
		return new PlusCalPrint(SourceLocation.unknown(), expr);
	}

	public static PlusCalEither either(List<List<PlusCalStatement>> cases) {
		return new PlusCalEither(SourceLocation.unknown(), cases);
	}

	public static PlusCalAwait await(TLAExpression cond) {
		return new PlusCalAwait(SourceLocation.unknown(), cond);
	}

	public static ModularPlusCalYield yield(TLAExpression expr) {
		return new ModularPlusCalYield(SourceLocation.unknown(), expr);
	}
}
