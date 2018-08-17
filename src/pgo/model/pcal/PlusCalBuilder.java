package pgo.model.pcal;

import java.util.Arrays;
import java.util.List;

import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAUnit;
import pgo.parser.Located;
import pgo.util.SourceLocation;

public class PlusCalBuilder {

	private PlusCalBuilder() {}

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

	public static PlusCalMacro macro(String name, List<String> args, PlusCalStatement... statements) {
		return new PlusCalMacro(SourceLocation.unknown(), name, args, Arrays.asList(statements));
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

}
