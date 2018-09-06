package pgo.model.mpcal;

import pgo.model.pcal.PlusCalMacro;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalProcesses;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAUnit;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class ModularPlusCalBlock extends ModularPlusCalNode {
	private final Located<String> name;
	private final List<PlusCalVariableDeclaration> variables;
	private final List<ModularPlusCalMappingMacro> mappingMacros;
	private final List<ModularPlusCalArchetype> archetypes;
	private final List<PlusCalMacro> macros;
	private final List<PlusCalProcedure> procedures;
	private final List<TLAUnit> units;
	private final List<ModularPlusCalInstance> instances;
	private final PlusCalProcesses processes;

	public ModularPlusCalBlock(SourceLocation location, Located<String> name,
	                           List<PlusCalVariableDeclaration> variables,
	                           List<TLAUnit> units, List<ModularPlusCalMappingMacro> mappingMacros,
	                           List<ModularPlusCalArchetype> archetypes, List<PlusCalMacro> macros,
	                           List<PlusCalProcedure> procedures, List<ModularPlusCalInstance> instances,
	                           PlusCalProcesses processes) {
		super(location);
		this.name = name;
		this.variables = variables;
		this.units = units;
		this.mappingMacros = mappingMacros;
		this.archetypes = archetypes;
		this.macros = macros;
		this.procedures = procedures;
		this.instances = instances;
		this.processes = processes;
	}

	@Override
	public ModularPlusCalBlock copy() {
		return new ModularPlusCalBlock(
				getLocation(),
				name,
				variables.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				units.stream().map(TLAUnit::copy).collect(Collectors.toList()),
				mappingMacros.stream().map(ModularPlusCalMappingMacro::copy).collect(Collectors.toList()),
				archetypes.stream().map(ModularPlusCalArchetype::copy).collect(Collectors.toList()),
				macros.stream().map(PlusCalMacro::copy).collect(Collectors.toList()),
				procedures.stream().map(PlusCalProcedure::copy).collect(Collectors.toList()),
				instances.stream().map(ModularPlusCalInstance::copy).collect(Collectors.toList()),
				processes.copy()
		);
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, variables, units, mappingMacros, archetypes, macros, procedures, instances, processes);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || obj.getClass() != getClass()) {
			return false;
		}
		ModularPlusCalBlock that = (ModularPlusCalBlock) obj;
		return name.getValue().equals(that.name.getValue()) &&
				Objects.equals(variables, that.variables) &&
				Objects.equals(units, that.units) &&
				Objects.equals(mappingMacros, that.mappingMacros) &&
				Objects.equals(archetypes, that.archetypes) &&
				Objects.equals(macros, that.macros) &&
				Objects.equals(procedures, that.procedures) &&
				Objects.equals(instances, that.instances) &&
				processes.equals(that.processes);
	}

	@Override
	public <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Located<String> getName() {
		return name;
	}

	public List<PlusCalVariableDeclaration> getVariables() {
		return Collections.unmodifiableList(variables);
	}

	public List<TLAUnit> getUnits() {
		return Collections.unmodifiableList(units);
	}

	public List<ModularPlusCalMappingMacro> getMappingMacros() {
		return Collections.unmodifiableList(mappingMacros);
	}

	public List<ModularPlusCalArchetype> getArchetypes() {
		return Collections.unmodifiableList(archetypes);
	}

	public List<PlusCalMacro> getMacros() {
		return Collections.unmodifiableList(macros);
	}

	public List<PlusCalProcedure> getProcedures() {
		return Collections.unmodifiableList(procedures);
	}

	public List<ModularPlusCalInstance> getInstances() {
		return Collections.unmodifiableList(instances);
	}

	public PlusCalProcesses getProcesses() {
		return processes;
	}
}
