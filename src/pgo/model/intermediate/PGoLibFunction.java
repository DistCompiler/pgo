package pgo.model.intermediate;

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

/**
 * Represents a TLA built-in function signature, and the equivalent Go function.
 * The TLA function might map to multiple Go functions so we need to store all
 * of these.
 *
 */
public class PGoLibFunction {
	// the TLA name
	private String name;
	// the return type
	PGoType ret;
	// the parameters, which map to the equivalent Go function
	private Map<Vector<PGoType>, String> paramsToGo;
	// map to whether the Go function is an object method or not
	private Map<Vector<PGoType>, Boolean> isObjMethod;

	public PGoLibFunction(String name, PGoType ret) {
		this.name = name;
		this.ret = ret;
		paramsToGo = new HashMap<>();
		isObjMethod = new HashMap<>();
	}

	public void addFuncSignature(Vector<PGoType> params, String goFuncName, boolean isObj) {
		paramsToGo.put(new Vector<>(params), goFuncName);
		isObjMethod.put(new Vector<>(params), isObj);
	}

	public String getName() {
		return name;
	}

	public PGoType getRetType() {
		return ret;
	}

	public String getGoName(Vector<PGoType> params) {
		return paramsToGo.get(params);
	}
}
