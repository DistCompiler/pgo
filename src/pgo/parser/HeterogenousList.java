package pgo.parser;

public final class HeterogenousList<First, Rest extends AbstractHeterogenousList<?, ?>> extends AbstractHeterogenousList<First, Rest> {

	private final First first;
	private final Rest rest;

	public HeterogenousList(First first, Rest rest) {
		this.first = first;
		this.rest = rest;
	}

	@Override
	public First getFirst() {
		return first;
	}

	@Override
	public Rest getRest() {
		return rest;
	}

	@Override
	public boolean isEmpty() {
		return false;
	}
}
