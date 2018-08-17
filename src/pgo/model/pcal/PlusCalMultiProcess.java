package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class PlusCalMultiProcess extends PlusCalProcesses {
	
	private List<PlusCalProcess> processes;
	
	public PlusCalMultiProcess(SourceLocation location, List<PlusCalProcess> processes) {
		super(location);
		this.processes = processes;
	}
	
	@Override
	public PlusCalMultiProcess copy() {
		return new PlusCalMultiProcess(getLocation(), processes.stream().map(PlusCalProcess::copy).collect(Collectors.toList()));
	}
	
	public List<PlusCalProcess> getProcesses(){
		return processes;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalProcessesVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((processes == null) ? 0 : processes.hashCode());
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
		PlusCalMultiProcess other = (PlusCalMultiProcess) obj;
		if (processes == null) {
			return other.processes == null;
		} else return processes.equals(other.processes);
	}

}
