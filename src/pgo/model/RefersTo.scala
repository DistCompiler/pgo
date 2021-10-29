package pgo.model

import scala.reflect.ClassTag

trait RefersTo[T <: RefersTo.HasReferences] extends Rewritable {
  private var refersTo_ : Option[T] = None
  def refersTo: T = refersTo_.get
  def setRefersTo(refersTo: T): this.type = {
    refersTo_ = Some(refersTo)
    this
  }
  def hasRefersTo: Boolean = refersTo_.nonEmpty

  override def decorateLike(succ: this.type): this.type =
    super.decorateLike(succ.setRefersTo(refersTo))
}

object RefersTo {
  def unapply(candidate: Any): Option[(RefersTo[_ <: HasReferences], _ <: HasReferences)] =
    candidate match {
      case refersTo: RefersTo[_] =>
        Some((refersTo, refersTo.refersTo))
      case _ => None
    }

  trait HasReferences
}
