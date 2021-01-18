package pgo.model.tla;

/**
 * In Scala, checked exceptions don't exist. To avoid massive (unnecessary) API breakage,
 * this interface escapes to Java to implement TLAUnit#accept with checked exceptions.
 */
interface TLAUnitVisitorThrowsHack {
    <T, E extends Throwable>T accept(TLAUnitVisitor<T, E> v) throws E;
}
