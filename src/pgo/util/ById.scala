package pgo.util

import scala.collection.{Factory, mutable}

/**
 * A wrapper class that compares the wrapped value by "pointer identity" (the JVM equivalent), bypassing
 * whatever value semantics the wrapped value might have.
 */
final class ById[+T <: AnyRef](val ref: T) {
  override def equals(obj: Any): Boolean =
    obj match {
      case other: ById[_] => ref eq other.ref
      case _ => false
    }

  override def toString: String = f"${ref.toString}@${hashCode()}%08x"

  override def hashCode(): Int = System.identityHashCode(ref)
}

object ById {
  def apply[T <: AnyRef](ref: T): ById[T] = new ById[T](ref)

  def unapply[T <: AnyRef](byId: ById[T]): Option[T] = Some(byId.ref)

  /**
   * Provides a factory of {{{Set[ById[V]]}}} from elements of type {{{V}}}
   */
  def setFactory[V <: AnyRef]: Factory[V,Set[ById[V]]] = new SetByIdFactory

  /**
   * Provides a factory of {{{Map[ById[K],V]]}}} from elements of type {{{(K,V)}}}
   */
  def mapFactory[K <: AnyRef,V]: Factory[(K,V),Map[ById[K],V]] = new MapByIdFactory

  private class SetByIdBuilder[V <: AnyRef] extends mutable.Builder[V, Set[ById[V]]] {
    private val underlying = Predef.Set.newBuilder[ById[V]]
    override def clear(): Unit = underlying.clear()
    override def result(): Set[ById[V]] = underlying.result()
    override def addOne(elem: V): this.type = {
      underlying += ById(elem)
      this
    }
  }

  private class SetByIdFactory[V <: AnyRef] extends Factory[V,Set[ById[V]]] {
    override def fromSpecific(it: IterableOnce[V]): Set[ById[V]] =
      it.iterator.map(ById(_)).toSet
    override def newBuilder: mutable.Builder[V, Set[ById[V]]] = new SetByIdBuilder
  }

  private class MapByIdBuilder[K <: AnyRef, V] extends mutable.Builder[(K,V), Map[ById[K],V]] {
    private val underlying = Predef.Map.newBuilder[ById[K],V]
    override def clear(): Unit = underlying.clear()
    override def result(): Map[ById[K], V] = underlying.result()
    override def addOne(elem: (K, V)): this.type = {
      underlying += ById(elem._1) -> elem._2
      this
    }
  }

  private class MapByIdFactory[K <: AnyRef, V] extends Factory[(K,V),Map[ById[K],V]] {
    override def fromSpecific(it: IterableOnce[(K, V)]): Map[ById[K], V] =
      it.iterator.map { case (k, v) => ById(k) -> v }.toMap
    override def newBuilder: mutable.Builder[(K, V), Map[ById[K], V]] = new MapByIdBuilder
  }
}
