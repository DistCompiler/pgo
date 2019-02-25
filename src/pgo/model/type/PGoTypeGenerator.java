package pgo.model.type;

import pgo.util.Origin;

import java.util.List;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Generates fresh PGoTypeVariables and PGoAbstractRecords.
 */
public class PGoTypeGenerator {
	private AtomicLong current = new AtomicLong(0);
	private String prefix;

	public PGoTypeGenerator(String prefix) {
		this.prefix = prefix;
	}

	public PGoTypeVariable getTypeVariable(List<Origin> origins) {
		long c = current.addAndGet(1);
		return new PGoTypeVariable(prefix + c, origins);
	}

	public PGoTypeAbstractRecord getAbstractRecord(List<Origin> origins) {
		long c = current.addAndGet(1);
		return new PGoTypeAbstractRecord(prefix + c, origins);
	}
}
