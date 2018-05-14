package pgo.util;

import pgo.model.intermediate.PGoVariable;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;

import java.util.Map;

public class PGoTypeUtil {
	private PGoTypeUtil() {}

	public static PGoType unifyAndSubstitute(PGoTypeSolver solver, PGoType type) {
		return type.substitute(unifyAndGetMapping(solver));
	}

	public static Map<PGoTypeVariable, PGoType> unifyAndGetMapping(PGoTypeSolver solver) {
		// unify once to get more type information
		solver.unify();
		return solver.getMapping();
	}

	public static PGoType substituteAndGetVariableType(PGoVariable var, Map<PGoTypeVariable, PGoType> mapping) {
		PGoType oldType = var.getType();
		PGoType newType = oldType.substitute(mapping);
		var.setType(newType);
		if (!newType.equals(oldType)) {
			var.setAsInferredType();
		}
		return newType;
	}

	public static PGoType substituteRealizeAndGetVariableType(PGoVariable var, Map<PGoTypeVariable, PGoType> mapping) {
		PGoType oldType = var.getType();
		PGoType newType = oldType.substitute(mapping).realize();
		var.setType(newType);
		if (!newType.equals(oldType)) {
			var.setAsInferredType();
		}
		return newType;
	}
}
