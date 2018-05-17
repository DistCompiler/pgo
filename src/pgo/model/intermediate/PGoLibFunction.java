package pgo.model.intermediate;

import java.util.*;

import pgo.model.type.*;
import pgo.model.type.PGoType;

/**
 * Represents a TLA built-in function signature, and the equivalent Go function.
 * The TLA function might map to multiple Go functions so we need to store all
 * of these.
 *
 */
public class PGoLibFunction {
	// the TLA name
	private String name;
	// the parameters, which map to the equivalent Go function
	private List<LibFuncInfo> paramsToGo;

	// Data class for Go function information.
	public class LibFuncInfo {
		private LibFuncInfo(String goName, boolean isObj, List<PGoType> params, PGoType returnType) {
			this.goName = goName;
			this.isObjMethod = isObj;
			this.params = params;
			this.returnType = returnType;
		}

		// the equivalent Go function
		private String goName;
		// true if the Go function is an object method
		private boolean isObjMethod;
		// params
		private List<PGoType> params;
		// return type
		private PGoType returnType;
		// this will be filled by withMapping
		private Map<PGoTypeVariable, PGoType> mapping;

		private LibFuncInfo withBoundTypes(List<PGoType> params, PGoType returnType) {
			return new LibFuncInfo(goName, isObjMethod, params, returnType);
		}

		public String getGoName() {
			return goName;
		}

		public boolean isObjMethod() {
			return isObjMethod;
		}

		public List<PGoType> getParams() {
			return Collections.unmodifiableList(params);
		}

		public PGoType getReturnType() {
			return returnType;
		}

		public PGoTypeFunction getFunctionType() { return new PGoTypeFunction(params, returnType); }

		public Map<PGoTypeVariable, PGoType> getMapping() {
			return mapping;
		}
	}

	public PGoLibFunction(String name) {
		this.name = name;
		paramsToGo = new ArrayList<>();
	}

	public void addFuncSignature(List<PGoType> params, String goFuncName, boolean isObj, PGoType returnType) {
		paramsToGo.add(new LibFuncInfo(goFuncName, isObj, params, returnType));
	}

	public String getName() {
		return name;
	}

	/**
	 * Helper method that returns the go func info with matching parameters.
	 * Also populates the argsToType map.
	 */
	public Optional<LibFuncInfo> getFunc(PGoTypeGenerator generator, List<PGoType> params) {
		for (LibFuncInfo fInfo : paramsToGo) {
			PGoTypeSolver solver = new PGoTypeSolver();
			PGoTypeFunction fresh = (PGoTypeFunction) generator.freshNamesFor(fInfo.getFunctionType());
			solver.accept(new PGoTypeConstraint(fresh, new PGoTypeFunction(params, fresh.getReturnType()), -1));
			try {
				solver.unify();
			} catch (PGoTypeUnificationException e) {
				continue;
			}
			PGoTypeFunction substituted = (PGoTypeFunction) fresh.substitute(solver.getMapping());
			return Optional.of(fInfo.withBoundTypes(substituted.getParamTypes(), substituted.getReturnType()));
		}
		return Optional.empty();
	}
}
