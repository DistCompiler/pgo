package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a process ID argument.
 *
 * FIXME this is a hack
 */
public class PGoTypeProcessId extends PGoPrimitiveType {
	public PGoTypeProcessId(Origin... origins) {
		super(origins);
	}

	public PGoTypeProcessId(List<Origin> origins) {
		super(origins);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeProcessId;
	}

	@Override
	public String toTypeName() {
		return "ProcessId";
	}

	@Override
	public String toGo() {
		throw new RuntimeException("Trying to convert process ID type to Go");
	}
}
