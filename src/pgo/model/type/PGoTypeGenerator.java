package pgo.model.type;

import java.util.HashMap;
import java.util.HashSet;
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
		return new PGoTypeVariable(prefix + Long.toString(c));
	}

	/**
	 * Generates fresh type variables while preserving the constraints
	 * within the type
	 */
	public PGoType freshNamesFor(PGoType ty) {
		HashSet<PGoTypeVariable> vars = new HashSet<>();
		ty.collectVariables(vars);
		HashMap<PGoTypeVariable, PGoType> m = new HashMap<>();
		for (PGoTypeVariable v : vars) {
			m.put(v, get());
		}
		return ty.substitute(m);
	}

}
