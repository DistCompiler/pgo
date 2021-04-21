package pgo.model

import java.lang.reflect.Constructor

trait Rewritable {
  import Rewritable._

  def productIterator: Iterator[Any]

  //def namedParts: Iterator[Any] = Iterator.empty

  def decorateLike(succ: this.type): this.type = succ

  def mapChildren(fn: Any => Any): this.type =
    withChildren(productIterator.map(fn))

  final def withChildren(children: Iterator[Any]): this.type = {
    val childrenSeq = children.toSeq
    if(childrenSeq.corresponds(productIterator)(_ forceEq _)) {
      this
    } else {
      decorateLike(constructLikeFromSeq(this, childrenSeq))
    }
  }

  final def shallowCopy(): this.type =
    decorateLike(constructLikeFromSeq(this, productIterator.toSeq))

  final def rewrite(strategy: Strategy = TopDownFirstStrategy)(fn: PartialFunction[Rewritable,Rewritable]): this.type =
    strategy.execute(this, fn).asInstanceOf[this.type]
}

object Rewritable {
  implicit class AnyOps(val lhs: Any) extends AnyVal {
    def forceEq(rhs: Any): Boolean =
      lhs.asInstanceOf[AnyRef] eq rhs.asInstanceOf[AnyRef]
  }

  trait Strategy {
    def execute(rewritable: Any, fn: PartialFunction[Rewritable,Rewritable]): Any
  }

  private val primitiveMap: Map[Class[_],Class[_]] = Map(
    Integer.TYPE -> classOf[Integer],
    java.lang.Byte.TYPE -> classOf[java.lang.Byte],
    Character.TYPE -> classOf[Character],
    java.lang.Boolean.TYPE -> classOf[java.lang.Boolean],
    java.lang.Double.TYPE -> classOf[java.lang.Double],
    java.lang.Float.TYPE -> classOf[java.lang.Float],
    java.lang.Long.TYPE -> classOf[java.lang.Float],
    java.lang.Short.TYPE -> classOf[java.lang.Short],
  )

  def constructLikeFromSeq[T](template: T, args: Seq[Any]): T = {
    val klass = template.getClass
    val constructor = klass.getConstructors()(0).asInstanceOf[Constructor[T]]
    val paramTypes = constructor.getParameterTypes
    require(paramTypes.length == args.size)
    (paramTypes.view zip args.view).zipWithIndex.foreach {
      case ((paramType, arg), idx) =>
        val effectiveParamType =
          if(paramType.isPrimitive) {
            primitiveMap(paramType)
          } else paramType
        require(effectiveParamType.isAssignableFrom(arg.getClass), s"type mismatch for argument $idx when constructing $klass")
    }
    constructor.newInstance(args:_*)
  }

  def transformSubNodes(rewritable: Any, fn: Any => Any): Any =
    rewritable match {
      case map: Map[_,_] =>
        val result = map.view.mapValues(fn).to(map.mapFactory)
        if(map.keysIterator.forall(k => map(k) forceEq result(k))) map
        else result
      case iterable: Iterable[_] =>
        val result = iterable.map(fn)
        if(result.corresponds(iterable)(_ forceEq _)) iterable
        else result
      case product: Product =>
        val resultArgs = product.productIterator.map(fn).toSeq
        if(product.productIterator.corresponds(resultArgs)(_ forceEq _)) product
        else constructLikeFromSeq(product, resultArgs)
      case any => any
    }

  object TopDownFirstStrategy extends Strategy {
    override def execute(rewritable: Any, fn: PartialFunction[Rewritable,Rewritable]): Any =
      rewritable match {
        case rewritable: Rewritable =>
          val result = fn.applyOrElse[Rewritable,Rewritable](rewritable, identity)
          if(result eq rewritable) {
            rewritable.mapChildren(this.execute(_, fn))
          } else {
            result
          }
        case otherwise =>
          transformSubNodes(otherwise, this.execute(_, fn))
      }
  }

  object BottomUpOnceStrategy extends Strategy {
    override def execute(rewritable: Any, fn: PartialFunction[Rewritable,Rewritable]): Any =
      rewritable match {
        case rewritable: Rewritable =>
          fn.applyOrElse(rewritable.mapChildren(this.execute(_, fn)), identity[Rewritable])
        case otherwise =>
          transformSubNodes(otherwise, this.execute(_, fn))
      }
  }
}
