package pgo.trans.intermediate;

import java.util.*;

import pgo.model.pcal.Procedure;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAFunctionDefinition;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.tla.PGoTLAUnit;
import pgo.scope.UID;

public class DefinitionRegistry {
	private Map<String, PGoTLAModule> modules;
	private Map<UID, PGoTLAUnit> definitions;
	private Map<UID, OperatorAccessor> operators;
	private Set<UID> globalVariables;
	private Set<UID> localVariables;
	private Map<UID, String> constants;
	private Map<UID, PGoTLAExpression> constantValues;
	private Map<UID, UID> references;
	private Map<String, Procedure> procedures;

	public DefinitionRegistry() {
		this.modules = new HashMap<>();
		this.definitions = new HashMap<>();
		this.operators = new HashMap<>();
		this.references = new HashMap<>();
		this.procedures = new HashMap<>();
		this.globalVariables = new HashSet<>();
		this.localVariables = new HashSet<>();
		this.constants = new HashMap<>();
		this.constantValues = new HashMap<>();
	}

	public Map<UID, UID> getReferences() {
		return references;
	}

	public void addModule(PGoTLAModule module) {
		if (!modules.containsKey(module.getName().getId())) {
			modules.put(module.getName().getId(), module);
		}
	}

	public void addOperatorDefinition(PGoTLAOperatorDefinition def) {
		if (!definitions.containsKey(def.getUID())) {
			definitions.put(def.getUID(), def);
		}
	}

	public void addOperator(UID uid, OperatorAccessor op) {
		operators.put(uid, op);
	}

	public void addFunctionDefinition(PGoTLAFunctionDefinition def) {
		if (!definitions.containsKey(def.getUID())) {
			definitions.put(def.getUID(), def);
		}
	}

	public void addProcedure(Procedure proc) {
		procedures.put(proc.getName(), proc);
	}

	public void addGlobalVariable(UID uid) {
		globalVariables.add(uid);
	}

	public void addLocalVariable(UID uid) {
		localVariables.add(uid);
	}

	public void addConstant(UID uid, String name) {
		constants.put(uid, name);
	}

	public UID followReference(UID from) {
		if (!references.containsKey(from)) {
			throw new RuntimeException("internal compiler error");
		}
		return references.get(from);
	}

	public OperatorAccessor findOperator(UID id) {
		if (!operators.containsKey(id)) {
			throw new RuntimeException("internal compiler error");
		}
		return operators.get(id);
	}

	public PGoTLAModule findModule(String name) {
		return modules.get(name);
	}

	public Procedure findProcedure(String name) {
		return procedures.get(name);
	}

	public boolean isGlobalVariable(UID ref) {
		return globalVariables.contains(ref);
	}

	public boolean isLocalVariable(UID ref) {
		return localVariables.contains(ref);
	}

	public boolean isConstant(UID ref) {
		return constants.containsKey(ref);
	}

	public Set<UID> getConstants() {
		return constants.keySet();
	}

	public String getConstantName(UID id) {
		if (!constants.containsKey(id)) {
			throw new RuntimeException("internal compiler error");
		}
		return constants.get(id);
	}

	public void setConstantValue(UID id, PGoTLAExpression value) {
		constantValues.put(id, value);
	}

	public PGoTLAExpression getConstantValue(UID id) {
		if (!constantValues.containsKey(id)) {
			throw new RuntimeException("internal compiler error");
		}
		return constantValues.get(id);
	}
}
