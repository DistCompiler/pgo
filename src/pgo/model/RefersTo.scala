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
  def unapply[T <: HasReferences](candidate: RefersTo[T]): Some[T] =
    Some(candidate.refersTo)

  trait HasReferences {
    def canonicalIdString: String
  }
}
