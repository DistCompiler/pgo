package pgo.model.intermediate;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Vector;

import pgo.model.intermediate.PGoCollectionType.PGoChan;
import pgo.model.intermediate.PGoCollectionType.PGoMap;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoCollectionType.PGoSlice;
import pgo.model.intermediate.PGoCollectionType.PGoTuple;
import pgo.model.intermediate.PGoPrimitiveType.PGoTemplateArgument;
import pgo.model.tla.TLAExprToType;

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
	private Map<Vector<PGoType>, LibFuncInfo> paramsToGo;
	// When getting a LibFuncInfo, maps the template argument from the info to
	// the actual type.
	private Map<PGoTemplateArgument, PGoType> argsToType;

	// Data class for Go function information.
	private class LibFuncInfo {
		private LibFuncInfo(String goFuncName, boolean isObj, PGoType retType) {
			this.goName = goFuncName;
			this.isObjMethod = isObj;
			this.ret = retType;
		}

		// the equivalent Go function
		private String goName;
		// true if the Go function is an object method
		private boolean isObjMethod;
		// return type
		private PGoType ret;
	}

	public PGoLibFunction(String name) {
		this.name = name;
		paramsToGo = new HashMap<>();
		argsToType = new HashMap<>();
	}

	public void addFuncSignature(Vector<PGoType> params, String goFuncName, boolean isObj, PGoType retType) {
		paramsToGo.put(new Vector<>(params), new LibFuncInfo(goFuncName, isObj, retType));
	}

	public String getName() {
		return name;
	}

	/**
	 * Helper method that returns the go func info with matching parameters.
	 * Also populates the argsToType map.
	 * 
	 * @return null if there are no matches
	 */
	private LibFuncInfo getFunc(Vector<PGoType> params) {
		LibFuncInfo ret = paramsToGo.get(params);
		if (ret != null) {
			return ret;
		}
		// check if we can match template arguments
		for (Entry<Vector<PGoType>, LibFuncInfo> sig : paramsToGo.entrySet()) {
			if (params.size() != sig.getKey().size()) {
				continue;
			}
			boolean good = true;
			// map the template argument to the actual type
			argsToType = new HashMap<>();
			for (int i = 0; i < params.size(); i++) {
				PGoType sigType = sig.getKey().get(i);
				PGoType paramType = params.get(i);
				if (sigType.hasTemplateArgs()) {
					Map<PGoTemplateArgument, PGoType> curArgMap = getTemplateArgs(sigType, paramType);
					if (curArgMap == null || checkTemplateArgConflict(argsToType, curArgMap)) {
						good = false;
						break;
					}
				} else if (TLAExprToType.compatibleType(sigType, paramType) == null) {
					good = false;
					break;
				}
			}
			if (good) {
				return sig.getValue();
			}
		}
		argsToType.clear();
		return null;
	}

	public String getGoName(Vector<PGoType> params) {
		LibFuncInfo func = getFunc(params);
		if (func == null) {
			return null;
		}
		return func.goName;
	}

	public Boolean isObjectMethod(Vector<PGoType> params) {
		LibFuncInfo func = getFunc(params);
		if (func == null) {
			return null;
		}
		return func.isObjMethod;
	}

	public PGoType getRetType(Vector<PGoType> params) {
		LibFuncInfo func = getFunc(params);
		if (func == null) {
			return null;
		}
		return fillTemplateArgs(func.ret);
	}

	// Given a return type, fill it with the template argument information in
	// argsToType.
	private PGoType fillTemplateArgs(PGoType type) {
		if (!type.hasTemplateArgs()) {
			return type;
		}
		if (type instanceof PGoTemplateArgument) {
			return argsToType.get((PGoTemplateArgument) type);
		}
		// If this is a tuple or map, we need to check all entries of tuple and
		// both key and val of map.
		if (type instanceof PGoTuple) {
			Vector<PGoType> elts = ((PGoTuple) type).getContainedTypes();
			Vector<PGoType> retTypes = new Vector<>();
			for (PGoType elt : elts) {
				retTypes.add(fillTemplateArgs(elt));
			}
			return new PGoTuple(retTypes, false);
		}

		if (type instanceof PGoMap) {
			PGoType eltType = fillTemplateArgs(((PGoMap) type).getElementType()),
					keyType = fillTemplateArgs(((PGoMap) type).getKeyType());
			return PGoType.inferFromGoTypeName("map[" + keyType.toTypeName() + "]" + eltType.toTypeName());
		}

		// We only need to check the element type.
		if (type instanceof PGoCollectionType) {
			PGoType eltType = fillTemplateArgs(((PGoCollectionType) type).getElementType());
			if (type instanceof PGoSlice) {
				return PGoType.inferFromGoTypeName("[]" + eltType.toTypeName());
			}
			if (type instanceof PGoChan) {
				return PGoType.inferFromGoTypeName("chan[" + eltType.toTypeName() + "]");
			}
			if (type instanceof PGoSet) {
				return PGoType.inferFromGoTypeName("set[" + eltType.toTypeName() + "]");
			}
		}

		assert false;
		return null;
	}

	// Return whether there is a conflict in template arguments, and add all new
	// arguments into first while also updating first with compatible types, if
	// appropriate. There is a conflict if we try to use two incompatible types
	// for the same template argument.
	private static boolean checkTemplateArgConflict(Map<PGoTemplateArgument, PGoType> first,
			Map<PGoTemplateArgument, PGoType> second) {
		for (Entry<PGoTemplateArgument, PGoType> e : second.entrySet()) {
			if (first.containsKey(e.getKey())) {
				PGoType compat = TLAExprToType.compatibleType(first.get(e.getKey()), e.getValue());
				if (compat == null) {
					return true;
				}
				first.put(e.getKey(), compat);
			} else {
				first.put(e.getKey(), e.getValue());
			}
		}
		return false;
	}

	/**
	 * Given two compatible types, find the types of second that correspond to
	 * the template arguments of first.
	 * 
	 * @return null if incompatible types are being compared, or if there is a
	 *         conflict in template arguments
	 */
	private static Map<PGoTemplateArgument, PGoType> getTemplateArgs(PGoType first, PGoType second) {
		assert (!second.hasTemplateArgs());
		if (TLAExprToType.compatibleType(first, second) == null) {
			return null;
		}
		Map<PGoTemplateArgument, PGoType> ret = new HashMap<>();
		if (first instanceof PGoTemplateArgument) {
			ret.put((PGoTemplateArgument) first, second);
			return ret;
		}

		// If this is a tuple or map, we need to check all entries of tuple and
		// both key and val of map.
		if (first instanceof PGoTuple) {
			Vector<PGoType> firstElts = ((PGoTuple) first).getContainedTypes(),
					secondElts = ((PGoTuple) second).getContainedTypes();
			if (firstElts.size() != secondElts.size()) {
				return null;
			}
			for (int i = 0; i < firstElts.size(); i++) {
				if (firstElts.get(i).hasTemplateArgs()) {
					Map<PGoTemplateArgument, PGoType> result = getTemplateArgs(firstElts.get(i), secondElts.get(i));
					if (result == null || checkTemplateArgConflict(ret, result)) {
						return null;
					}
				}
			}
			return ret;
		}

		if (first instanceof PGoMap) {
			if (((PGoMap) first).getKeyType().hasTemplateArgs()) {
				Map<PGoTemplateArgument, PGoType> result = getTemplateArgs(((PGoMap) first).getKeyType(),
						((PGoMap) second).getKeyType());
				if (result == null || checkTemplateArgConflict(ret, result)) {
					return null;
				}
			}
			if (((PGoMap) first).getElementType().hasTemplateArgs()) {
				Map<PGoTemplateArgument, PGoType> result = getTemplateArgs(((PGoMap) first).getElementType(),
						((PGoMap) second).getElementType());
				if (result == null || checkTemplateArgConflict(ret, result)) {
					return null;
				}
			}
			return ret;
		}

		if (first instanceof PGoCollectionType) {
			return getTemplateArgs(((PGoCollectionType) first).getElementType(),
					((PGoCollectionType) second).getElementType());
		}

		return null;
	}
}
