package pgo.util

import scala.collection.mutable
import java.lang.ref.SoftReference
import java.lang.ref.ReferenceQueue
import scala.compiletime.ops.double
import scala.reflect.TypeTest

final class SoftHashMap[K <: AnyRef, V](using
    val nullKTest: TypeTest[K | Null, K],
):
  private enum KWrapper:
    case Direct(key: K)
    private case Indirect(ref: SoftReference[K])

    // require hashCodeOf to be set correctly
    this match
      case Direct(key) => // always ok
      case Indirect(ref) =>
        require(KWrapper.hashCodeOf.contains(ref))

    override def hashCode(): Int =
      this match
        case Direct(key)   => key.hashCode()
        case Indirect(ref) => KWrapper.hashCodeOf(ref)

    private def kVal: K | Null =
      this match
        case Direct(key)   => key
        case Indirect(ref) => ref.get()

    private def ref: SoftReference[K] =
      this match
        case Direct(key)   => ???
        case Indirect(ref) => ref

    override def equals(that: Any): Boolean =
      that match
        case that: KWrapper =>
          (this.kVal, that.kVal) match
            case (null, null) =>
              // This is for dead refs, so it can only happen
              // if we're looking for a reclaimed key to remove it.
              // Just check ptr eq, because that's all that's left.
              this.ref eq that.ref
            case (key1: K, key2: K) =>
              // Regardless of wrappers, we actually found 2 keys.
              // "normal" case.
              key1 == key2
            case _ =>
              // We assume null vs K is not reasonable, and resolve
              // it as "this can't be what you're looking for"
              false
        case _ => false

  private object KWrapper:
    private val referenceQueue = ReferenceQueue[K]()

    def makeIndirect(key: K): KWrapper =
      // This snippet cleans up any nulled soft refs we're holding onto.
      // This assumes the fn is called semi regularly, if it is used at all.
      var refToRemove = referenceQueue.poll()
      while refToRemove ne null do
        // cast because we know it's a soft ref
        implMap -= Indirect(refToRemove.asInstanceOf[SoftReference[K]])
        hashCodeOf -= refToRemove.asInstanceOf[SoftReference[K]]
        refToRemove = referenceQueue.poll()
      end while

      val ref = SoftReference(key, referenceQueue)
      hashCodeOf.update(ref, key.hashCode())
      Indirect(ref)
    end makeIndirect

    // 2nd map, which relates the ptr value of SoftReference to its hashCode,
    // even if the ref has already been reclaimed. This is crucial for hash map
    // correctness, because otherwise a reclaimed soft ref will no longer hash
    // to the right value, and will appear like a completely fresh key.
    private val hashCodeOf = mutable.HashMap[SoftReference[K], Int]()
  end KWrapper

  private val implMap = mutable.HashMap[KWrapper, V]()

  def get(key: K): Option[V] =
    implMap.get(KWrapper.Direct(key))

  def put(key: K, value: V): Option[V] =
    implMap.put(KWrapper.makeIndirect(key), value)
end SoftHashMap
