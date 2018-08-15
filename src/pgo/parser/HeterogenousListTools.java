package pgo.parser;

public final class HeterogenousListTools {

	private HeterogenousListTools() {}

	private static final EmptyHeterogenousList EMPTY_HETEROGENOUS_LIST = new EmptyHeterogenousList();

	public static EmptyHeterogenousList empty(){
		return EMPTY_HETEROGENOUS_LIST;
	}

	public static <First, Rest extends AbstractHeterogenousList<?, ?>> HeterogenousList<First, Rest> cons(First first, Rest rest) {
		return new HeterogenousList<>(first, rest);
	}

	public static <First> First first(AbstractHeterogenousList<First, ?> list) {
		return list.getFirst();
	}

	public static <Rest extends AbstractHeterogenousList<?, ?>> Rest rest(AbstractHeterogenousList<?, Rest> list) {
		return list.getRest();
	}

	public static <Second> Second second(AbstractHeterogenousList<?, ? extends AbstractHeterogenousList<Second, ?>> list) {
		return first(rest(list));
	}

	public static <Third> Third third(AbstractHeterogenousList<?, ? extends AbstractHeterogenousList<?, ? extends  AbstractHeterogenousList<Third, ?>>> list) {
		return second(rest(list));
	}

	public static <Fourth> Fourth fourth(AbstractHeterogenousList<?, ? extends AbstractHeterogenousList<?, ? extends AbstractHeterogenousList<?, ? extends AbstractHeterogenousList<Fourth, ?>>>> list) {
		return third(rest(list));
	}

}
