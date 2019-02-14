package pgo.model.type;

import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Supplier;

/**
 * Generates fresh PGoTypeVariables and infers types from Go type names.
 */
public class PGoTypeGenerator implements Supplier<PGoTypeVariable> {
	private AtomicLong current = new AtomicLong(0);
	private String prefix;

	public PGoTypeGenerator(String prefix) {
		this.prefix = prefix;
	}

	@Override
	public PGoTypeVariable get() {
		long c = current.addAndGet(1);
		return new PGoTypeVariable(prefix + c);
	}
}
