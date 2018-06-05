package pgo.util;

/**
 * A plain data object representing a pair.
 */
public class Pair<A, B> {
	public A first;
	public B second;

	public Pair(A a, B b) {
		first = a;
		second = b;
	}
}
