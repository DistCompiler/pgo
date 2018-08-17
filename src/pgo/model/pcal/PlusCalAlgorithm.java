package pgo.model.pcal;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import pgo.model.tla.TLAUnit;
import pgo.parser.Located;
import pgo.util.SourceLocation;

public class PlusCalAlgorithm extends PlusCalNode {

	private final Located<String> name;

	private final PlusCalFairness fairness;
	private final List<PlusCalVariableDeclaration> variables;
	private final List<PlusCalMacro> macros;
	private final List<PlusCalProcedure> procedures;
	private final List<TLAUnit> units;

	private final PlusCalProcesses processes;

	public PlusCalAlgorithm(SourceLocation location, PlusCalFairness fairness, Located<String> name, List<PlusCalVariableDeclaration> variables,
							List<PlusCalMacro> macros, List<PlusCalProcedure> procedures, List<TLAUnit> units, PlusCalProcesses processes) {
		super(location);
		this.fairness = fairness;
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
				fairness,
				name,
				variables.stream().map(PlusCalVariableDeclaration::copy).collect(Collectors.toList()),
				macros.stream().map(PlusCalMacro::copy).collect(Collectors.toList()),
				procedures.stream().map(PlusCalProcedure::copy).collect(Collectors.toList()),
				units.stream().map(TLAUnit::copy).collect(Collectors.toList()),
				processes.copy());
	}

	public PlusCalFairness getFairness() { return fairness; }

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
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		PlusCalAlgorithm that = (PlusCalAlgorithm) o;
		return Objects.equals(name, that.name) &&
				fairness == that.fairness &&
				Objects.equals(variables, that.variables) &&
				Objects.equals(macros, that.macros) &&
				Objects.equals(procedures, that.procedures) &&
				Objects.equals(units, that.units) &&
				Objects.equals(processes, that.processes);
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, fairness, variables, macros, procedures, units, processes);
	}
}
