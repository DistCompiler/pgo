package pgo.util;

/**
 * This class represents an empty {@link HeterogenousList}. This will always be the final tail of such a list.
 *
 * <p>Interestingly, all heterogenous lists are subtypes of this list so it is actually possible to pass a
 * longer list as where a shorter one was needed and have everything work.</p>
 */
public class EmptyHeterogenousList {
	/**
	 * @return whether this list is empty
	 */
	public boolean isEmpty(){ return true; }

	/**
	 * Produces a new list with {@param first} as the head element and the current list as the tail
	 * @param first the first element of the new list
	 * @param <First> the type of {@param first}
	 * @return a new list with {@param first} as the first element and this list as the tail
	 */
	public <First> HeterogenousList<First, ?> cons(First first) {
		return new HeterogenousList<>(first, this);
	}
}
