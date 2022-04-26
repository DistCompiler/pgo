package pgo.model

import org.scalatest.funsuite.AnyFunSuite

// can't be fields of an object; it messes with constructor signature
sealed abstract class Node extends Rewritable

final case class Split[L <: Node, R <: Node](left: L, right: R) extends Node {
  override def toString: String = f"Split($left,$right)@${System.identityHashCode(this)}%08x"
}

final case class Split3[L <: Node, M <: Node, R <: Node](left: L, mid: M, right: R) extends Node {
  override def toString: String = f"Split3($left,$mid,$right)@${System.identityHashCode(this)}%08x"
}

final case class Def(i: Int) extends Node with RefersTo.HasReferences {
  override def toString: String = f"Def($i)@${System.identityHashCode(this)}%08x"
  override def canonicalIdString: String = toString
}

final case class DefPlus[P <: Node](i: Int, plus: P) extends Node with RefersTo.HasReferences {
  override def toString: String = f"DefPlus($i,$plus)@${System.identityHashCode(this)}%08x"
  override def canonicalIdString: String = toString
}

final case class Ref() extends Node with RefersTo[RefersTo.HasReferences] {
  override def toString: String = f"Ref()@${System.identityHashCode(this)}%08x"
}

class RewritableTests extends AnyFunSuite {
  private val d1 = Def(1)
  private val d2 = Def(2)
  private val ast1 = Split(d1, Ref().setRefersTo(d1))

  test("namedParts returns immediate sub-nodes") {
    assert(ast1.namedParts.toList == List(d1))
  }

  test("rewrite preserves cross-references") {
    val ast2 = ast1.rewrite(Rewritable.BottomUpOnceStrategy) {
      case `d1` => d2
    }

    assert(ast2.left eq d2)
    assert(ast2.right.refersTo eq d2)
  }

  test("rewrite handles transitive references") {
    val d1 = Def(1)
    val dp2 = DefPlus(2, Ref().setRefersTo(d1))
    val ast = Split3(d1, dp2, Ref().setRefersTo(dp2))

    val result = ast.rewrite(Rewritable.BottomUpOnceStrategy) {
      case dd1 if dd1 eq d1 => d1.shallowCopy()
    }

    assert(result.left ne d1)
    assert(result.mid ne dp2)
    assert(result.right ne ast.right)

    assert(result.mid.plus.refersTo eq result.left)
    assert(result.right.refersTo eq result.mid)
  }

  test("rewrite handles recursive references") {
    val r = Ref()
    val ast = DefPlus(1, r)
    r.setRefersTo(ast)

    println("---")

    val result = ast.rewrite(Rewritable.BottomUpOnceStrategy) {
      case rr if rr eq r => r.shallowCopy()
    }

    assert(result.plus ne r)
    assert(result.plus.refersTo eq result)
  }

  test("rewrite handles mutually recursive references") {
    val dp1r = Ref()
    val dp1 = DefPlus(1, dp1r)
    val dp2 = DefPlus(2, Ref().setRefersTo(dp1))
    dp1r.setRefersTo(dp2)
    val ast = Split(dp1, dp2)

    val result = ast.rewrite(Rewritable.BottomUpOnceStrategy) {
      case ddp1r if ddp1r eq dp1r => dp1r.shallowCopy()
    }

    assert(result.left ne dp1)
    assert(result.right ne dp2)

    assert(result.left.plus.refersTo eq result.right)
    assert(result.right.plus.refersTo eq result.left)
  }

}
