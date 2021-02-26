package pgo.model.type;

import pgo.util.Origin;

import java.util.List;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Generates fresh PGoTypeVariables and PGoAbstractRecords.
 */
public class TypeGenerator {
	private final AtomicLong current = new AtomicLong(0);
	private final String prefix;

	public TypeGenerator(String prefix) {
		this.prefix = prefix;
	}

	public TypeVariable getTypeVariable(List<Origin> origins) {
		long c = current.addAndGet(1);
		return new TypeVariable(prefix + c, origins);
	}

	public AbstractRecordType getAbstractRecord(List<Origin> origins) {
		long c = current.addAndGet(1);
		return new AbstractRecordType(prefix + c, origins);
	}
}
