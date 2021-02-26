package pgo.model.pcal;

import pgo.model.mpcal.ModularPlusCalBlockVisitor;
import pgo.util.SourceLocation;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class PlusCalSingleProcess extends PlusCalProcesses {
	
	private final List<PlusCalStatement> body;
	
	public PlusCalSingleProcess(SourceLocation location, List<PlusCalStatement> body) {
		super(location);
		this.body = body;
	}
	
	@Override
	public PlusCalSingleProcess copy() {
		return new PlusCalSingleProcess(
				getLocation(),
				body.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}
	
	public List<PlusCalStatement> getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalProcessesVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public <T, E extends Throwable> T accept(ModularPlusCalBlockVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		PlusCalSingleProcess that = (PlusCalSingleProcess) o;
		return Objects.equals(body, that.body);
	}

	@Override
	public int hashCode() {
		return Objects.hash(body);
	}
}
