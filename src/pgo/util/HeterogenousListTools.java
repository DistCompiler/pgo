package pgo.util;

public final class HeterogenousListTools {

	private HeterogenousListTools() {}

	private static final EmptyHeterogenousList EMPTY_HETEROGENOUS_LIST = new EmptyHeterogenousList();

	public static EmptyHeterogenousList empty(){
		return EMPTY_HETEROGENOUS_LIST;
	}

	public static <First, Rest extends EmptyHeterogenousList> HeterogenousList<First, Rest> cons(First first, Rest rest) {
		return new HeterogenousList<>(first, rest);
	}

}
