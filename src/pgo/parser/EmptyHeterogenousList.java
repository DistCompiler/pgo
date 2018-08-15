package pgo.parser;

public final class EmptyHeterogenousList extends AbstractHeterogenousList<Void, EmptyHeterogenousList> {
	@Override
	public Void getFirst() {
		return null;
	}

	@Override
	public EmptyHeterogenousList getRest() {
		return this;
	}

	@Override
	public boolean isEmpty() {
		return true;
	}
}
