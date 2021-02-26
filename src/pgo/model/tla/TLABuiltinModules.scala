package pgo.model.tla

import pgo.scope.UID
import pgo.util.SourceLocation

object TLABuiltinModules {
  abstract class TLABuiltinModule(id: String) extends TLADefinitionOne {
    override val getUID: UID = new UID()
    override val identifier: TLAIdentifier = new TLAIdentifier(SourceLocation.unknown(), id)

    def members: List[TLABuiltinOperator]
    lazy val memberMap: Map[TLAIdentifier,TLABuiltinOperator] =
      members.flatMap(m => (m.identifier -> m) :: m.aliasIDs.map(a => a -> m)).toMap

    def member(id: String): TLABuiltinOperator =
      memberMap(new TLAIdentifier(SourceLocation.unknown(), id))

    override def arity: Int = 0

    override def isModuleInstance: Boolean = false

    override def scope: Map[TLAIdentifier, TLADefinitionOne] = Map.empty
  }

  final class TLABuiltinOperator(id: String, override val arity: Int, aliases: String*) extends TLADefinitionOne {
    override val getUID: UID = new UID()
    override val identifier: TLAIdentifier = new TLAIdentifier(SourceLocation.unknown(), id)
    val aliasIDs: List[TLAIdentifier] = aliases.map(new TLAIdentifier(SourceLocation.unknown(), _)).toList

    override def isModuleInstance: Boolean = false

    override def scope: Map[TLAIdentifier, TLADefinitionOne] = Map.empty
  }

  // these operators are always available
  object Intrinsics extends TLABuiltinModule("") {
    override val members: List[TLABuiltinOperator] = List(
      // logic
      new TLABuiltinOperator("/\\", 2, aliases = "\\land"),
      new TLABuiltinOperator("\\/", 2, aliases = "\\lor"),
      new TLABuiltinOperator("\\lnot", 1, aliases = "~", "\\neg"),
      new TLABuiltinOperator("=>", 2),
      new TLABuiltinOperator("<=>", 2, aliases = "\\equiv"),
      new TLABuiltinOperator("TRUE", 0),
      new TLABuiltinOperator("FALSE", 0),
      new TLABuiltinOperator("BOOLEAN", 0),

      // sets
      new TLABuiltinOperator("=", 2),
      new TLABuiltinOperator("#", 2), // /=
      new TLABuiltinOperator("\\in", 2),
      new TLABuiltinOperator("\\notin", 2),
      new TLABuiltinOperator("\\cap", 2, aliases = "\\intersect"),
      new TLABuiltinOperator("\\cup", 2, aliases = "\\union"),
      new TLABuiltinOperator("\\subseteq", 2),
      new TLABuiltinOperator("\\", 2),
      new TLABuiltinOperator("SUBSET", 1),
      new TLABuiltinOperator("UNION", 1),

      // functions
      new TLABuiltinOperator("DOMAIN", 1),

      // strings
      new TLABuiltinOperator("STRING", 0),

      // action
      new TLABuiltinOperator("'", 1),
      new TLABuiltinOperator("ENABLED", 1),
      new TLABuiltinOperator("UNCHANGED", 1),
      new TLABuiltinOperator("\\cdot", 2),

      // temporal
      new TLABuiltinOperator("[]", 1),
      new TLABuiltinOperator("<>", 1),
      new TLABuiltinOperator("~>", 2),
      new TLABuiltinOperator("-+->", 2),
    )
  }

  val builtinModules: Map[TLAIdentifier,TLABuiltinModule] = List(
    TLC,
    Sequences, FiniteSets, Bags,
    Peano, ProtoReals, Naturals, Integers, Reals,
  ).map(mod => mod.identifier -> mod).toMap

  object TLC extends TLABuiltinModule("TLC") {
    override val members: List[TLABuiltinOperator] = List(
      new TLABuiltinOperator("Print", 2),
      new TLABuiltinOperator("PrintT", 1),
      new TLABuiltinOperator("Assert", 2),
      new TLABuiltinOperator("JavaTime", 0),
      new TLABuiltinOperator(":>", 2),
      new TLABuiltinOperator("@@", 2),
      new TLABuiltinOperator("Permutations", 1),
      new TLABuiltinOperator("SortSeq", 2),
    )
  }

  object Sequences extends TLABuiltinModule("Sequences") {
    override val members: List[TLABuiltinOperator] = List(
      new TLABuiltinOperator("Seq", 1),
      new TLABuiltinOperator("Len", 1),
      new TLABuiltinOperator("\\o", 2, aliases = "\\circ"),
      new TLABuiltinOperator("Append", 2),
      new TLABuiltinOperator("Head", 1),
      new TLABuiltinOperator("Tail", 1),
      new TLABuiltinOperator("SubSeq", 3),
      new TLABuiltinOperator("SelectSeq", 2),
    )
  }

  object FiniteSets extends TLABuiltinModule("FiniteSets") {
    override val members: List[TLABuiltinOperator] = List(
      new TLABuiltinOperator("IsFiniteSet", 1),
      new TLABuiltinOperator("Cardinality", 1),
    )
  }

  object Bags extends TLABuiltinModule("Bags") {
    override val members: List[TLABuiltinOperator] = List(
      new TLABuiltinOperator("IsABag", 1),
      new TLABuiltinOperator("BagToSet", 1),
      new TLABuiltinOperator("SetToBag", 1),
      new TLABuiltinOperator("BagIn", 2),
      new TLABuiltinOperator("EmptyBag", 0),
      new TLABuiltinOperator("CopiesIn", 2),
      new TLABuiltinOperator("\\oplus", 2, aliases = "(+)"),
      new TLABuiltinOperator("\\ominus", 2, aliases = "(-)"),
      new TLABuiltinOperator("BagUnion", 1),
      new TLABuiltinOperator("\\sqsubseteq", 2),
      new TLABuiltinOperator("SubBag", 1),
      new TLABuiltinOperator("BagOfAll", 2),
      new TLABuiltinOperator("BagCardinality", 1),
    )
  }

  object Peano extends TLABuiltinModule("Peano") {
    override val members: List[TLABuiltinOperator] = List(
      new TLABuiltinOperator("PeanoAxioms", 3),
      new TLABuiltinOperator("Succ", 0),
      new TLABuiltinOperator("Nat", 0),
      new TLABuiltinOperator("Zero", 0),
    )
  }

  object ProtoReals extends TLABuiltinModule("ProtoReals") {
    override val members: List[TLABuiltinOperator] = Peano.members ++ List(
      new TLABuiltinOperator("IsModelOfReals", 4),
      new TLABuiltinOperator("RM", 0),
      new TLABuiltinOperator("Real", 0),
      new TLABuiltinOperator("Infinity", 0),
      new TLABuiltinOperator("MinusInfinity", 0),
      new TLABuiltinOperator("+", 2),
      new TLABuiltinOperator("*", 2),
      new TLABuiltinOperator("\\leq", 2, aliases = "<=", "=<"),
      new TLABuiltinOperator("-", 2),
      new TLABuiltinOperator("/", 2),
      new TLABuiltinOperator("Int", 0),
      new TLABuiltinOperator("^", 2),
    )
  }

  object Naturals extends TLABuiltinModule("Naturals") {
    override val members: List[TLABuiltinOperator] = List(
      ProtoReals.member("Nat"),
      ProtoReals.member("+"),
      ProtoReals.member("-"),
      ProtoReals.member("*"),
      ProtoReals.member("^"),
      ProtoReals.member("\\leq"),
      new TLABuiltinOperator("\\geq", 2, aliases = ">="),
      new TLABuiltinOperator("<", 2),
      new TLABuiltinOperator(">", 2),
      new TLABuiltinOperator("..", 2),
      new TLABuiltinOperator("\\div", 2),
      new TLABuiltinOperator("%", 2),
    )
  }

  object Integers extends TLABuiltinModule("Integers") {
    override val members: List[TLABuiltinOperator] = Naturals.members ++ List(
      ProtoReals.member("Int"),
      new TLABuiltinOperator("-_", 1),
    )
  }

  object Reals extends TLABuiltinModule("Reals") {
    override val members: List[TLABuiltinOperator] = Integers.members ++ List(
      ProtoReals.member("Real"),
      ProtoReals.member("/"),
      ProtoReals.member("Infinity"),
    )
  }
}
