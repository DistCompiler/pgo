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
  def unapply[T <: HasReferences](candidate: RefersTo[T])(implicit classTag: ClassTag[T]): Option[T] =
    candidate match {
      case refersTo: RefersTo[T @unchecked] if classTag.runtimeClass.isInstance(refersTo.refersTo) =>
        Some(refersTo.refersTo)
      case _ => None
    }

  trait HasReferences {
    def canonicalIdString: String
  }
}
