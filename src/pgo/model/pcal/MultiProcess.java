package pgo.model.pcal;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

public class MultiProcess extends Processes {
	
	private List<PcalProcess> processes;
	
	public MultiProcess(SourceLocation location, List<PcalProcess> processes) {
		super(location);
		this.processes = processes;
	}
	
	@Override
	public MultiProcess copy() {
		return new MultiProcess(getLocation(), processes.stream().map(PcalProcess::copy).collect(Collectors.toList()));
	}
	
	public List<PcalProcess> getProcesses(){
		return processes;
	}

	@Override
	public <T, E extends Throwable> T accept(ProcessesVisitor<T, E> v) throws E {
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
		MultiProcess other = (MultiProcess) obj;
		if (processes == null) {
			if (other.processes != null)
				return false;
		} else if (!processes.equals(other.processes))
			return false;
		return true;
	}

}
