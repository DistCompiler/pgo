package pgo.util;

public final class HeterogenousList<First, Rest extends EmptyHeterogenousList> extends EmptyHeterogenousList {

	private final First first;
	private final Rest rest;

	public HeterogenousList(First first, Rest rest) {
		this.first = first;
		this.rest = rest;
	}

	public First getFirst() {
		return first;
	}

	public Rest getRest() {
		return rest;
	}

	public boolean isEmpty() {
		return false;
	}
}
