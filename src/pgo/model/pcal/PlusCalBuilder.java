package pgo.model.pcal;

import pgo.model.mpcal.*;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAUnit;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class PlusCalBuilder {
	private PlusCalBuilder() {}

	public static PlusCalDefaultInitValue PLUSCAL_DEFAULT_INIT_VALUE = new PlusCalDefaultInitValue(SourceLocation.unknown());

	public static PlusCalAlgorithm algorithm(String name, List<PlusCalVariableDeclaration> vars, List<PlusCalMacro> macros, List<PlusCalProcedure> procedures, List<TLAUnit> units, PlusCalLabeledStatements... statements) {
		return new PlusCalAlgorithm(SourceLocation.unknown(), PlusCalFairness.UNFAIR,
				new Located<>(SourceLocation.unknown(), name), vars, macros, procedures, units,
				new PlusCalSingleProcess(SourceLocation.unknown(), Arrays.asList(statements)));
	}

	public static PlusCalAlgorithm algorithm(String name, List<PlusCalVariableDeclaration> vars, List<PlusCalMacro> macros, List<PlusCalProcedure> procedures, List<TLAUnit> units, PlusCalProcess... processes) {
		return new PlusCalAlgorithm(SourceLocation.unknown(), PlusCalFairness.UNFAIR,
				new Located<>(SourceLocation.unknown(), name), vars, macros, procedures, units,
				new PlusCalMultiProcess(SourceLocation.unknown(), Arrays.asList(processes)));
	}

	public static ModularPlusCalBlock mpcal(String name, List<ModularPlusCalArchetype> archetypes,
										 List<ModularPlusCalMappingMacro> mappingMacros,
										 List<ModularPlusCalInstance> instances,
										 List<PlusCalVariableDeclaration> vars,
										 List<PlusCalMacro> macros, List<PlusCalProcedure> procedures,
										 List<TLAUnit> units, PlusCalProcess... processes) {
		return new ModularPlusCalBlock(SourceLocation.unknown(), new Located<>(SourceLocation.unknown(), name),
				vars, units, mappingMacros, archetypes, macros, procedures, instances,
				new PlusCalMultiProcess(SourceLocation.unknown(), Arrays.asList(processes)));
	}

	public static PlusCalVariableDeclaration pcalVarDecl(String name, boolean isRef, boolean isSet,
	                                                     TLAExpression value) {
		return new PlusCalVariableDeclaration(
				SourceLocation.unknown(), new Located<>(SourceLocation.unknown(), name), isRef, isSet, value);
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

	public static PlusCalCall call(String target, TLAExpression... args) {
		return new PlusCalCall(SourceLocation.unknown(), target, Arrays.asList(args));
	}

	public static PlusCalReturn returnS() {
		return new PlusCalReturn(SourceLocation.unknown());
	}

	public static PlusCalGoto gotoS(String target) {
		return new PlusCalGoto(SourceLocation.unknown(), target);
	}

	public static PlusCalAssignment assign(TLAExpression... expressions) {
		assert (expressions.length % 2) == 0;
		List<PlusCalAssignmentPair> pairs = new ArrayList<>();

		int i = 0;
		TLAExpression lhs = null;
		for (TLAExpression e : expressions) {
			if (i == 0) {
				lhs = e;
				i++;
			} else {
				pairs.add(new PlusCalAssignmentPair(SourceLocation.unknown(), lhs, e));
				i = 0;
			}
		}

		return new PlusCalAssignment(SourceLocation.unknown(), pairs);
	}

	public static PlusCalPrint printS(TLAExpression expr) {
		return new PlusCalPrint(SourceLocation.unknown(), expr);
	}

	public static PlusCalWhile whileS(TLAExpression condition, List<PlusCalStatement> body) {
		return new PlusCalWhile(SourceLocation.unknown(), condition, body);
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
