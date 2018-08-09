package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.model.tla.TLAUnit;
import pgo.parser.Located;
import pgo.util.SourceLocation;

public class PlusCalAlgorithm extends PlusCalNode {

	private Located<String> name;

	private List<PlusCalVariableDeclaration> variables;
	private List<PlusCalMacro> macros;
	private List<PlusCalProcedure> procedures;
	private List<TLAUnit> units;

	private PlusCalProcesses processes;

	public PlusCalAlgorithm(SourceLocation location, Located<String> name, List<PlusCalVariableDeclaration> variables,
							List<PlusCalMacro> macros, List<PlusCalProcedure> procedures, List<TLAUnit> units, PlusCalProcesses processes) {
		super(location);
		this.name = name;
		this.variables = variables;
		this.macros = macros;
		this.procedures = procedures;
		this.units = units;
		this.processes = processes;
	}

	@Override
	public PlusCalAlgorithm copy() {
		return new PlusCalAlgorithm(
				getLocation(),
				name,
				variables.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				macros.stream().map(PlusCalMacro::copy).collect(Collectors.toList()),
				procedures.stream().map(PlusCalProcedure::copy).collect(Collectors.toList()),
				units.stream().map(TLAUnit::copy).collect(Collectors.toList()),
				processes.copy());
	}

	public Located<String> getName() {
		return name;
	}

	public List<PlusCalVariableDeclaration> getVariables() {
		return variables;
	}

	public List<PlusCalMacro> getMacros() {
		return macros;
	}

	public List<PlusCalProcedure> getProcedures() {
		return procedures;
	}

	public List<TLAUnit> getUnits(){
		return units;
	}

	public PlusCalProcesses getProcesses() {
		return processes;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((macros == null) ? 0 : macros.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((procedures == null) ? 0 : procedures.hashCode());
		result = prime * result + ((processes == null) ? 0 : processes.hashCode());
		result = prime * result + ((units == null) ? 0 : units.hashCode());
		result = prime * result + ((variables == null) ? 0 : variables.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PlusCalAlgorithm other = (PlusCalAlgorithm) obj;
		if (macros == null) {
			if (other.macros != null)
				return false;
		} else if (!macros.equals(other.macros))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (procedures == null) {
			if (other.procedures != null)
				return false;
		} else if (!procedures.equals(other.procedures))
			return false;
		if (processes == null) {
			if (other.processes != null)
				return false;
		} else if (!processes.equals(other.processes))
			return false;
		if (units == null) {
			if (other.units != null)
				return false;
		} else if (!units.equals(other.units))
			return false;
		if (variables == null) {
			if (other.variables != null)
				return false;
		} else if (!variables.equals(other.variables))
			return false;
		return true;
	}

}
