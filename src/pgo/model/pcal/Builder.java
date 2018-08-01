package pgo.model.pcal;

import java.util.Arrays;
import java.util.List;

import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAUnit;
import pgo.parser.Located;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public class Builder {

	private Builder() {}

	public static Algorithm algorithm(String name, List<VariableDeclaration> vars, List<Macro> macros, List<Procedure> procedures, List<PGoTLAUnit> units, LabeledStatements... statements) {
		return new Algorithm(SourceLocation.unknown(), new Located<>(SourceLocation.unknown(), name), vars, macros,
				procedures, units, new SingleProcess(SourceLocation.unknown(), Arrays.asList(statements)));
	}

	public static Algorithm algorithm(String name, List<VariableDeclaration> vars, List<Macro> macros, List<Procedure> procedures, List<PGoTLAUnit> units, PcalProcess... processes) {
		return new Algorithm(SourceLocation.unknown(), new Located<>(SourceLocation.unknown(), name), vars, macros,
				procedures, units, new MultiProcess(SourceLocation.unknown(), Arrays.asList(processes)));
	}

	public static Macro macro(String name, List<String> args, Statement... statements) {
		return new Macro(SourceLocation.unknown(), name, args, Arrays.asList(statements));
	}

	public static Label label(String name) {
		return new Label(SourceLocation.unknown(), name, Label.Modifier.NONE);
	}

	public static LabeledStatements labeled(Label label, Statement... statements) {
		return new LabeledStatements(SourceLocation.unknown(), label, Arrays.asList(statements));
	}

	public static MacroCall macroCall(String name, PGoTLAExpression... args) {
		return new MacroCall(SourceLocation.unknown(), name, Arrays.asList(args));
	}

	public static Print printS(PGoTLAExpression expr) {
		return new Print(SourceLocation.unknown(), expr);
	}

}
