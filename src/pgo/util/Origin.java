package pgo.util;

/**
 * 
 * Where something was Derived from. Should be implemented by anything relevant.
 * 
 * The Visitor allows code to inspect what the origin actually was, ideally at a high
 * level.
 *
 */
public interface Origin {
	<T, E extends Throwable> T accept(OriginVisitor<T, E> v) throws E;
}
