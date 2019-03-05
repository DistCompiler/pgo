package pgo.trans.intermediate;

import pgo.InternalCompilerError;
import pgo.model.golang.type.GoType;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.*;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.scope.UID;

import java.util.*;
import java.util.function.Consumer;

public class DefinitionRegistry {
	private final Map<String, TLAModule> modules;
	private final Map<UID, TLAUnit> definitions;
	private final Map<UID, OperatorAccessor> operators;
	private final Map<UID, GoType> globalVariableTypes;
	private final Set<UID> localVariables;
	private final Map<UID, String> constants;
	private final Map<UID, TLAExpression> constantValues;
	private final Map<UID, UID> references;
	private final Map<String, PlusCalProcedure> procedures;
	private final Map<String, ModularPlusCalArchetype> archetypes;
	private final Map<UID, PGoType> readValueTypes;
	private final Map<UID, PGoType> writtenValueTypes;
	private final Map<String, ModularPlusCalMappingMacro> mappingMacros;
	private final Map<UID, Integer> labelsToLockGroups;
	private final Map<Integer, Set<UID>> lockGroupsToVariableReads;
	private final Map<Integer, Set<UID>> lockGroupsToVariableWrites;
	private final Map<Integer, Set<TLAExpression>> lockGroupsToResourceReads;
	private final Map<Integer, Set<TLAExpression>> lockGroupsToResourceWrites;
	private final Set<UID> archetypeResources;
	private final Set<UID> protectedGlobalVariables;
	private final Map<UID, boolean[]> signatures;

	public DefinitionRegistry() {
		this.modules = new HashMap<>();
		this.definitions = new HashMap<>();
		this.operators = new HashMap<>();
		this.references = new HashMap<>();
		this.procedures = new HashMap<>();
		this.archetypes = new HashMap<>();
		this.readValueTypes = new HashMap<>();
		this.writtenValueTypes = new HashMap<>();
		this.mappingMacros = new HashMap<>();
		this.globalVariableTypes = new HashMap<>();
		this.localVariables = new HashSet<>();
		this.constants = new HashMap<>();
		this.constantValues = new HashMap<>();
		this.labelsToLockGroups = new HashMap<>();
		this.lockGroupsToVariableReads = new HashMap<>();
		this.lockGroupsToVariableWrites = new HashMap<>();
		this.lockGroupsToResourceReads = new HashMap<>();
		this.lockGroupsToResourceWrites = new HashMap<>();
		this.archetypeResources = new HashSet<>();
		this.protectedGlobalVariables = new HashSet<>();
		this.signatures = new HashMap<>();
	}

	public Map<UID, UID> getReferences() {
		return references;
	}

	public void addModule(TLAModule module) {
		if (!modules.containsKey(module.getName().getId())) {
			modules.put(module.getName().getId(), module);
		}
	}

	public void addOperatorDefinition(TLAOperatorDefinition def) {
		if (!definitions.containsKey(def.getUID())) {
			definitions.put(def.getUID(), def);
		}
	}

	public void addOperator(UID uid, OperatorAccessor op) {
		operators.put(uid, op);
	}

	public void addFunctionDefinition(TLAFunctionDefinition def) {
		if (!definitions.containsKey(def.getUID())) {
			definitions.put(def.getUID(), def);
		}
	}

	public void addProcedure(PlusCalProcedure proc) {
		procedures.put(proc.getName(), proc);
	}

	public void addArchetype(ModularPlusCalArchetype archetype) {
		archetypes.put(archetype.getName(), archetype);
	}

	public void addReadAndWrittenValueTypes(ModularPlusCalArchetype archetype, PGoTypeGenerator generator) {
		for (PlusCalVariableDeclaration declaration : archetype.getParams()) {
			readValueTypes.put(declaration.getUID(), generator.getTypeVariable(Collections.singletonList(declaration)));
			writtenValueTypes.put(
					declaration.getUID(), generator.getTypeVariable(Collections.singletonList(declaration)));
		}
	}

	public void addMappingMacro(ModularPlusCalMappingMacro mappingMacro) {
		mappingMacros.put(mappingMacro.getName(), mappingMacro);
	}

	public void addGlobalVariable(UID uid) {
		globalVariableTypes.put(uid, null);
	}

	public void updateGlobalVariableType(UID uid, GoType type) {
		if (!globalVariableTypes.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		globalVariableTypes.put(uid, type);
	}

	public void addLocalVariable(UID uid) {
		localVariables.add(uid);
	}

	public void addConstant(UID uid, String name) {
		constants.put(uid, name);
	}

	public UID followReference(UID from) {
		if (!references.containsKey(from)) {
			throw new InternalCompilerError();
		}
		return references.get(from);
	}

	public OperatorAccessor findOperator(UID id) {
		if (!operators.containsKey(id)) {
			throw new InternalCompilerError();
		}
		return operators.get(id);
	}

	public TLAModule findModule(String name) {
		return modules.get(name);
	}

	public PlusCalProcedure findProcedure(String name) {
		return procedures.get(name);
	}

	public ModularPlusCalArchetype findArchetype(String name) {
		return archetypes.get(name);
	}

	public PGoType getReadValueType(UID varUID) {
		return readValueTypes.get(varUID);
	}

	public void updateReadValueType(UID uid, PGoType type) {
		if (!readValueTypes.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		readValueTypes.put(uid, type);
	}

	public void forEachReadValueType(Consumer<UID> action) {
		readValueTypes.keySet().forEach(action);
	}

	public PGoType getWrittenValueType(UID varUID) {
		return writtenValueTypes.get(varUID);
	}

	public void updateWrittenValueType(UID uid, PGoType type) {
		if (!writtenValueTypes.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		writtenValueTypes.put(uid, type);
	}

	public void forEachWrittenValueType(Consumer<UID> action) {
		writtenValueTypes.keySet().forEach(action);
	}

	public ModularPlusCalMappingMacro findMappingMacro(String name) {
		return mappingMacros.get(name);
	}

	public boolean isGlobalVariable(UID ref) {
		return globalVariableTypes.containsKey(ref);
	}

	public GoType getGlobalVariableType(UID uid) {
		return globalVariableTypes.get(uid);
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
			throw new InternalCompilerError();
		}
		return constants.get(id);
	}

	public void setConstantValue(UID id, TLAExpression value) {
		constantValues.put(id, value);
	}

	public Optional<TLAExpression> getConstantValue(UID id) {
		return Optional.ofNullable(constantValues.get(id));
	}

	public Set<UID> globalVariables() {
		return globalVariableTypes.keySet();
	}

	public void addLabelToLockGroup(UID labelUID, int lockGroup) {
		if (labelsToLockGroups.containsKey(labelUID)) {
			throw new InternalCompilerError();
		}
		labelsToLockGroups.put(labelUID, lockGroup);
	}

	public int getLockGroup(UID labelUID) {
		return labelsToLockGroups.get(labelUID);
	}

	public int getNumberOfLockGroups() {
		return 1 + labelsToLockGroups.values().stream()
				.max(Comparator.comparingInt(Integer::intValue))
				.orElse(-1);
	}

	public int getLockGroupOrDefault(UID labelUID, int defaultValue) {
		return labelsToLockGroups.getOrDefault(labelUID, defaultValue);
	}

	public void addVariableReadToLockGroup(UID varUID, int lockGroup) {
		lockGroupsToVariableReads.putIfAbsent(lockGroup, new HashSet<>());
		lockGroupsToVariableReads.get(lockGroup).add(varUID);
	}

	public void addVariableWriteToLockGroup(UID varUID, int lockGroup) {
		lockGroupsToVariableWrites.putIfAbsent(lockGroup, new HashSet<>());
		lockGroupsToVariableWrites.get(lockGroup).add(varUID);
	}

	public void addResourceReadToLockGroup(TLAExpression resource, int lockGroup) {
		lockGroupsToResourceReads.putIfAbsent(lockGroup, new HashSet<>());
		lockGroupsToResourceReads.get(lockGroup).add(resource);
	}

	public void addResourceWriteToLockGroup(TLAExpression resource, int lockGroup) {
		lockGroupsToResourceWrites.putIfAbsent(lockGroup, new HashSet<>());
		lockGroupsToResourceWrites.get(lockGroup).add(resource);
	}

	public Set<TLAExpression> getResourceReadsInLockGroup(int lockGroup) {
		return Collections.unmodifiableSet(lockGroupsToResourceReads.getOrDefault(lockGroup, Collections.emptySet()));
	}

	public Set<TLAExpression> getResourceWritesInLockGroup(int lockGroup) {
		return Collections.unmodifiableSet(lockGroupsToResourceWrites.getOrDefault(lockGroup, Collections.emptySet()));
	}

	public Set<UID> getVariableReadsInLockGroup(int lockGroup) {
		return Collections.unmodifiableSet(lockGroupsToVariableReads.getOrDefault(lockGroup, Collections.emptySet()));
	}

	public Set<UID> getVariableWritesInLockGroup(int lockGroup) {
		return Collections.unmodifiableSet(lockGroupsToVariableWrites.getOrDefault(lockGroup, Collections.emptySet()));
	}

	public void addArchetypeResource(UID uid) {
		this.archetypeResources.add(uid);
	}

	public boolean isArchetypeResource(UID uid) {
		return this.archetypeResources.contains(uid);
	}

	public void addProtectedGlobalVariable(UID varUID) {
		protectedGlobalVariables.add(varUID);
	}

	public Set<UID> protectedGlobalVariables() {
		return Collections.unmodifiableSet(protectedGlobalVariables);
	}

	public Optional<boolean[]> getSignature(UID uid) {
		return Optional.ofNullable(signatures.get(uid));
	}

	public void putSignature(UID uid, boolean[] signature) {
		if (signatures.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		signatures.put(uid, signature);
	}
}
