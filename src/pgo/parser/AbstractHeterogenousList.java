package pgo.parser;

public abstract class AbstractHeterogenousList<First, Rest extends AbstractHeterogenousList<?, ?>> {

	public abstract First getFirst();
	public abstract Rest getRest();
	public abstract boolean isEmpty();

}
