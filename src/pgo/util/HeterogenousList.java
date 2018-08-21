package pgo.util;

/**
 * Represents a typesafe heterogenous list.
 *
 * <p>This list is very limited compared to the typical {@link java.util.List}, but in exchange you can
 * prepend elements of any type to it and retrieve them without having to risk a type-unsafe downcast.</p>
 *
 * <p>The lists's properties are achieved by creating a linked list where the type of the tail is irrelevant
 * to each node of the list but is known to the typechecker, such that it can infer complete types for
 * the two accessor methods.</p>
 *
 * <p>The most notable caveat is that it is either very hard or impossible to deal with arbitrarily-long lists
 * of this kind. Luckily the main use for them is as the result of {@link pgo.parser.AbstractSequenceGrammar},
 * whose length is known at compile-time.</p>
 * @param <First> the type of the head of this list
 * @param <Rest> the type of the tail of this list, recursively also a list.
 */
public final class HeterogenousList<First, Rest extends EmptyHeterogenousList> extends EmptyHeterogenousList {

	private final First first;
	private final Rest rest;

	public HeterogenousList(First first, Rest rest) {
		this.first = first;
		this.rest = rest;
	}

	/**
	 * @return the head, or first element of this list
	 */
	public First getFirst() {
		return first;
	}

	/**
	 * @return the tail of this list, which is also a list.
	 */
	public Rest getRest() {
		return rest;
	}

	@Override
	public boolean isEmpty() {
		return false;
	}
}
