package pgo.model

import pgo.model.Rewritable.BottomUpOnceStrategy
import pgo.util.IdMap

import scala.reflect.ClassTag

trait RefersTo[T] extends Rewritable { _: Rewritable =>
  private var refersTo_ : Option[T] = None
  def refersTo: T = refersTo_.get
  def setRefersTo(refersTo: T): this.type = {
    refersTo_ = Some(refersTo)
    this
  }

  override def decorateLike(succ: this.type): this.type =
    super.decorateLike(succ.setRefersTo(refersTo))
}

object RefersTo {
  def unapply[T](candidate: Any)(implicit tag: ClassTag[T]): Option[T] =
    candidate match {
      case refersTo: RefersTo[_] =>
        refersTo.refersTo match {
          case tag(refersTo) =>
            Some(refersTo)
          case _ => None
        }
      case _ => None
    }

  def eqFixpoint[T](init: T)(fn: T => T): T = {
    import Rewritable._
    var tmp = init
    var nextTmp = fn(tmp)
    while(!(tmp forceEq nextTmp)) {
      tmp = nextTmp
      nextTmp = fn(tmp)
    }
    tmp
  }

  final class Renamer[RefType <: AnyRef](implicit tag: ClassTag[RefType]) {
    private var renamings = IdMap.empty[RefType,RefType]

    def addRenaming(from: RefType, to: RefType): this.type = {
      renamings = renamings.updated(from, to)
      this
    }

    def addRenamings(renamings: IterableOnce[(RefType,RefType)]): this.type = {
      renamings.iterator.foreach {
        case (from, to) => addRenaming(from, to)
      }
      this
    }

    private object RenamedTo {
      def unapply(node: Rewritable): Option[(Rewritable with RefersTo[RefType], RefType)] = {
        node match {
          case node: Rewritable with RefersTo[RefType] if tag.runtimeClass.isInstance(node.refersTo) =>
            // catch transitive renamings
            def rec(ref: RefType): Option[RefType] =
              renamings.get(ref)
                .filter(_ ne ref) // avoid renaming loops
                .flatMap(rec)
                .orElse(Some(ref))

            rec(node.refersTo).map((node, _))
          case _ => None
        }
      }
    }

    def apply[N <: Rewritable](node: N): N = {
      if(renamings.nonEmpty) {
        node.rewrite(strategy = BottomUpOnceStrategy) {
          case RenamedTo(ref, to) => ref.shallowCopy().setRefersTo(to)
        }
      } else node
    }

    def captureRenaming[T <: RefType with Rewritable](ref: T, fn: T=>T): T = {
      val mappedRef = fn(apply(ref))
      if(mappedRef ne ref) {
        addRenaming(ref, mappedRef)
      }
      mappedRef
    }

    def captureRenamingAny[T <: RefType with Rewritable](ref: T, fn: Any=>Any): T =
      captureRenaming(ref, (t: T) => fn(t).asInstanceOf[T])

    def mapConserveRenaming[T <: RefType with Rewritable](refs: List[T], fn: T=>T): List[T] =
      refs.mapConserve(captureRenaming(_, fn))

    def mapConserveRenamingAny[T <: RefType with Rewritable](refs: List[T], fn: Any=>Any): List[T] =
      mapConserveRenaming(refs, (t: T) => fn(t).asInstanceOf[T])
  }
}
