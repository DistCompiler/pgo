package pgo.util

import java.io.OutputStream
import java.nio.charset.StandardCharsets

import scala.collection.{View, mutable}
import scala.util.control.NonFatal
import scala.util.{Failure, Success, Try}

import pgo.model.SourceLocation
import pgo.model.tla.*
import pgo.model.tla.BuiltinModules.TLABuiltinOperator
import pgo.parser.TLAParser
import pgo.trans.TLARenderPass

import Description.*

object TLAExprInterpreter {
  private def mkExceptionDesc(
      reason: Description,
      badValue: Option[TLAValue],
      badNode: Option[TLANode],
  ): Description =
    d"evaluation error ($reason)${badValue match {
        case None           => d""
        case Some(badValue) =>
          d", due to value ${badValue.describe}"
      }}${badNode match {
        case None          => d""
        case Some(badNode) =>
          d" at ${badNode.sourceLocation.longDescription}".ensureLineBreakBefore.indented
      }}"

  final case class Unsupported() extends RuntimeException("unsupported") {
    private var _badNode: Option[TLANode] = None
    def badNode: Option[TLANode] = _badNode

    private var _hint: Option[Description] = None
    def hint: Option[Description] = _hint

    def ensureNodeInfo(node: TLANode): this.type = {
      _badNode = _badNode.orElse(Some(node))
      this
    }

    def ensureHint(hint: Description): this.type = {
      _hint = _hint.orElse(Some(hint))
      this
    }

    def describe: Description =
      mkExceptionDesc(
        reason =
          d"operation not supported by current configuration ${hint.map(h => d"[$h]").getOrElse(d"")}",
        badValue = None,
        badNode = badNode,
      )
  }
  final case class TypeError() extends RuntimeException("TLA+ type error") {
    private var _badValue: Option[TLAValue] = None
    private var _badNode: Option[TLANode] = None
    def badValue: Option[TLAValue] = _badValue
    def badNode: Option[TLANode] = _badNode

    def ensureNodeInfo(node: TLANode): this.type = {
      _badNode = _badNode.orElse(Some(node))
      this
    }

    def ensureValueInfo(value: TLAValue): this.type = {
      _badValue = _badValue.orElse(Some(value))
      this
    }

    def describe: Description =
      mkExceptionDesc(d"TLA+ type error", badValue, badNode)
  }

  sealed abstract class TLAValue extends Product:
    final override def toString: String =
      describe.linesIterator.mkString("\n")

    def describe: Description

    final def asBoolean: Boolean =
      this match
        case TLAValueBool(value) => value
        case _ => throw RuntimeException(s"$this is not a boolean")
    end asBoolean

    final def asInt: Int =
      this match
        case TLAValueNumber(value) => value
        case _ => throw RuntimeException(s"$this is not an integer")
    end asInt

    final def asString: String =
      this match
        case TLAValueString(value) => value
        case _ => throw RuntimeException(s"$this is not a string")
    end asString

    final def asMap: Map[TLAValue, TLAValue] =
      this match
        case TLAValueTuple(value) =>
          value.view.zipWithIndex
            .map: (elem, idx) =>
              TLAValueNumber(idx + 1) -> elem
            .toMap
        case TLAValueFunction(value) =>
          value
        case _ => throw RuntimeException(s"$this cannot be viewed as a map")
    end asMap

    final def asVector: Vector[TLAValue] =
      this match
        case TLAValueTuple(value) => value
        case _ => throw RuntimeException(s"$this cannot be viewed as a vector")
    end asVector

    final def contains(elem: TLAValue): Boolean =
      (this, elem) match
        case (TLAValueTuple(value), TLAValueNumber(idx)) =>
          value.indices.contains(idx - 1)
        case (TLAValueFunction(value), TLAValueTuple(Vector(key, elemValue))) =>
          value.get(key).contains(elemValue)
        case (TLAValueSet(value), elem) =>
          value.contains(elem)
        case _ =>
          throw RuntimeException(
            s"$this cannot be checked for membership of $elem",
          )
    end contains

    extension (opt: Option[TLAValue])
      private inline def orErr(inline field: String): TLAValue =
        opt match
          case None => throw RuntimeException(s"not found $field in $this")
          case Some(value) => value
      end orErr

    final def apply(field: String): TLAValue =
      this.get(field).orErr(field)
    end apply

    final def apply(field: Int): TLAValue =
      this.get(field).orErr(field.toString)

    final def apply(field: TLAValue): TLAValue =
      this.get(field).orErr(field.toString)

    final def get(field: Int): Option[TLAValue] =
      this.get(TLAValueNumber(field))

    final def get(field: String): Option[TLAValue] =
      this.get(TLAValueString(field))

    final def get(field: TLAValue): Option[TLAValue] =
      (this, field) match
        case (TLAValueString(value), TLAValueNumber(idx)) =>
          value
            .lift(idx - 1)
            .map: value =>
              TLAValueString(value.toString)
        case (TLAValueTuple(Vector()), _)                => None
        case (TLAValueTuple(value), TLAValueNumber(idx)) =>
          value.lift(idx - 1)
        case (TLAValueFunction(value), field) =>
          value.get(field)
        case _ =>
          throw RuntimeException(s"cannot index $this by value $field")
    end get

    def asTLCBinFmt: geny.Writable =
      val self = this
      new geny.Writable:
        final def writeBytesTo(_out: OutputStream): Unit =
          val out = java.io.DataOutputStream(java.io.BufferedOutputStream(_out))

          val stringUniqTable = mutable.HashMap[String, Int]()

          def writeByte(byte: Byte): Unit =
            out.writeByte(byte)

          def writeArray(arr: Array[Byte]): Unit =
            out.write(arr, 0, arr.length)
          end writeArray

          def writeShort(short: Short): Unit =
            out.writeShort(short)

          def writeInt(int: Int): Unit =
            out.writeInt(int)

          def writeNat(x: Int): Unit =
            if x > 0x7fff
            then writeInt(-x)
            else writeShort(x.toShort)

          def impl(value: TLAValue): Unit =
            value match
              case TLAValueModel(name) =>
                throw RuntimeException("cannot serialize TLA+ model value")
              case TLAValueBool(value) =>
                writeByte(0) // BOOLEANVALUE
                writeByte(if value then 1 else 0)
              case TLAValueNumber(value) =>
                writeByte(1) // INTVALUE
                writeInt(value)
              case TLAValueString(value) =>
                writeByte(3) // STRINGVALUE
                val tok =
                  stringUniqTable.getOrElseUpdate(value, stringUniqTable.size)
                writeInt(tok)
                writeInt(
                  -1,
                ) // == tok if the string "is a variable"... probably not relevant

                // TLC below a certain version only handles ASCII, but should handle UTF-8 in future.
                val strBytes = value.getBytes(StandardCharsets.UTF_8)
                writeInt(strBytes.length)
                writeArray(strBytes)
              case TLAValueSet(value) =>
                writeByte(5) // SETENUMVALUE
                writeInt(
                  -value.size,
                ) // negative value means not normalized. We can't guarantee same sort order as TLC
                value.foreach(impl)
              case TLAValueTuple(value) =>
                writeByte(7) // TUPLEVALUE
                writeNat(value.length)
                value.foreach(impl)
              case TLAValueFunction(value) =>
                // Note: "record" is also an option here, but we don't have an explicit representation for it.
                //       I assume TLC will forgive me if I encode something that could have been a "record" as this more
                //       general construct.
                writeByte(9) // FCNRCDVALUE
                writeNat(value.size)
                writeByte(
                  2,
                ) // 0 if a compressed interval (we don't support this), 1 if normalized (no, requires sorting), 2 if neither
                value.foreach: (k, v) =>
                  impl(k)
                  impl(v)
              case TLAValueLambda(fn) =>
                throw RuntimeException("cannot serialize TLA+ lambda value")
          end impl

          try
            impl(self)
          finally
            out.flush()
        end writeBytesTo
    end asTLCBinFmt

    def asTLCBinFmtGZIP: geny.Writable =
      new geny.Writable:
        def writeBytesTo(_out: java.io.OutputStream): Unit =
          val out = java.util.zip.GZIPOutputStream(_out)
          try
            asTLCBinFmt.writeBytesTo(out)
          finally
            out.finish()
        end writeBytesTo
    end asTLCBinFmtGZIP
  end TLAValue

  object TLAValue:
    private val parseCache = SoftHashMap[String, TLAValue]()

    def parseFromString(str: String): TLAValue =
      synchronized:
        parseCache.get(str) match
          case None =>
            val expr = TLAParser.readExpression(
              new SourceLocation.UnderlyingString(str),
              str,
              // Integers needed for prefix `-`, and TLC needed for `:>` and `@@`
              definitions =
                BuiltinModules.Integers.members ::: BuiltinModules.TLC.members,
            )
            val value = interpret(expr)(using Map.empty)
            parseCache.put(str, value)
            value
          case Some(value) => value
    end parseFromString

    def parseFromTLCBinFmt(readable: geny.Readable): TLAValue =
      readable.readBytesThrough: _in =>
        val handlesBuffer = mutable.ArrayBuffer[TLAValue]()
        val in = java.io.DataInputStream(java.io.BufferedInputStream(_in))
        def readOneNat(): Int =
          val short = in.readShort()
          if short >= 0
          then short
          else
            val short2 = in.readShort()
            val int = (short.toInt << 16) | (short2.toInt & 0xffff)
            -int
        end readOneNat

        def readOneString(): String =
          val _ = in.readInt() // drop "token"
          val _ = in.readInt() // drop var stuff
          val size = in.readInt()
          val bytes = in.readNBytes(size)
          String(bytes, StandardCharsets.UTF_8)
        end readOneString

        def withHandle(fn: => TLAValue): TLAValue =
          val idx = handlesBuffer.size
          handlesBuffer += null
          val result = fn
          handlesBuffer(idx) = result
          result
        end withHandle

        def readOneValue(): TLAValue =
          in.readByte() match
            case 0 =>
              TLAValueBool:
                in.readByte() match
                  case 0 => false
                  case 1 => true
                  case b => throw RuntimeException(s"invalid boolean value $b")
            case 1 =>
              TLAValueNumber(in.readInt())
            case 3 =>
              withHandle:
                TLAValueString(readOneString())
            case 4 =>
              withHandle:
                val size = in.readInt().abs
                TLAValueFunction:
                  (0 until size).view
                    .map: _ =>
                      in.readByte() match
                        case 26 =>
                          val idx = readOneNat()
                          handlesBuffer(idx) -> readOneValue()
                        case _ =>
                          withHandle(
                            TLAValueString(readOneString()),
                          ) -> readOneValue()
                    .toMap
            case 5 =>
              withHandle:
                val size = in.readInt().abs
                TLAValueSet(Set.tabulate(size)(_ => readOneValue()))
            case 7 =>
              withHandle:
                val size = readOneNat()
                TLAValueTuple(Vector.tabulate(size)(_ => readOneValue()))
            case 9 =>
              withHandle:
                val size = readOneNat()
                in.readByte() match
                  case 0 => throw RuntimeException("TODO: compressed interval")
                  case 1 | 2 =>
                    TLAValueFunction(
                      (0 until size).view
                        .map(_ => (readOneValue(), readOneValue()))
                        .toMap,
                    )
                  case b =>
                    throw RuntimeException(s"corrupted function/record: $b")
            case 26 =>
              val idx = readOneNat()
              handlesBuffer(idx)
            case b =>
              throw RuntimeException(s"unrecognized type code $b")
        end readOneValue

        readOneValue()
    end parseFromTLCBinFmt

    def parseFromTLCBinFmtGZIP(readable: geny.Readable): TLAValue =
      readable.readBytesThrough: _in =>
        val in = java.util.zip.GZIPInputStream(_in)
        parseFromTLCBinFmt(in)
    end parseFromTLCBinFmtGZIP

    given ordering: Ordering[TLAValue] with
      def compare(left: TLAValue, right: TLAValue): Int =
        Ordering[String].compare(left.productPrefix, right.productPrefix) match
          case 0 =>
            (left, right) match
              case (TLAValueBool(left), TLAValueBool(right)) =>
                Ordering[Boolean].compare(left, right)
              case (TLAValueNumber(left), TLAValueNumber(right)) =>
                Ordering[Int].compare(left, right)
              case (TLAValueString(left), TLAValueString(right)) =>
                Ordering[String].compare(left, right)
              case (TLAValueModel(left), TLAValueModel(right)) =>
                Ordering[String].compare(left, right)
              case (TLAValueSet(left), TLAValueSet(right)) =>
                val leftArr = left.toArray.sortInPlace
                val rightArr = right.toArray.sortInPlace
                Ordering.Implicits
                  .seqOrdering[mutable.ArraySeq, TLAValue]
                  .compare(leftArr, rightArr)
              case (TLAValueTuple(left), TLAValueTuple(right)) =>
                Ordering.Implicits
                  .seqOrdering[Vector, TLAValue]
                  .compare(left, right)
              case (TLAValueFunction(left), TLAValueFunction(right)) =>
                val leftArr = left.toArray.sortInPlace
                val rightArr = right.toArray.sortInPlace
                Ordering.Implicits
                  .seqOrdering[mutable.ArraySeq, (TLAValue, TLAValue)]
                  .compare(leftArr, rightArr)
              case (TLAValueLambda(left), TLAValueLambda(right)) =>
                Ordering[Int].compare(left.hashCode(), right.hashCode())
              case _ => throw RuntimeException("unreachable")
          case ord => ord
      end compare
    end ordering
  end TLAValue

  final case class TLAValueModel(name: String) extends TLAValue {
    override def describe: Description =
      name.toDescription
  }
  final case class TLAValueBool(value: Boolean) extends TLAValue {
    override def describe: Description =
      if (value) {
        d"TRUE"
      } else {
        d"FALSE"
      }
  }
  final case class TLAValueNumber(value: Int) extends TLAValue {
    override def describe: Description =
      value.toString.description
  }
  final case class TLAValueString(value: String) extends TLAValue {
    override def describe: Description =
      TLARenderPass.describeExpr(TLAString(value))
  }
  final case class TLAValueSet(value: Set[TLAValue]) extends TLAValue {
    override def describe: Description =
      d"{${value.toArray.sortInPlace
          .map(_.describe)
          .separateBy(d", ")}}"
  }
  final case class TLAValueTuple(value: Vector[TLAValue]) extends TLAValue {
    override def describe: Description =
      d"<<${value.view
          .map(_.describe)
          .separateBy(d", ")}>>"
  }
  final case class TLAValueFunction(value: Map[TLAValue, TLAValue])
      extends TLAValue {
    override def describe: Description = {
      if (value.isEmpty) {
        "[x \\in {} |-> x]".description
      } else {
        d"(${value.toArray.sortInPlace
            .map: (key, value) =>
              d"(${key.describe}) :> (${value.describe})".indented
            .separateBy(d" @@ ")})"
      }
    }
  }

  final case class TLAValueLambda(fn: PartialFunction[List[TLAValue], TLAValue])
      extends TLAValue {
    override def describe: Description =
      d"LAMBDA ${String.format("%x", System.identityHashCode(fn))}"
  }

  private[pgo] def valueFn[T](fn: PartialFunction[TLAValue, T]): TLAValue => T =
    fn.orElse { (badValue: TLAValue) =>
      throw TypeError().ensureValueInfo(badValue)
    }

  extension (value: TLAValue)
    private[pgo] def narrowMatch[T](fn: PartialFunction[TLAValue, T]): T =
      fn.applyOrElse(
        value,
        { (badValue: TLAValue) =>
          throw TypeError().ensureValueInfo(badValue)
        },
      )

  extension [N <: TLANode](node: N)
    private[pgo] final def narrowMatch[T](fn: PartialFunction[N, T]): T =
      try
        fn.applyOrElse(
          node,
          { (badNode: TLANode) =>
            throw Unsupported().ensureNodeInfo(badNode)
          },
        )
      catch
        case err: TypeError                => throw err.ensureNodeInfo(node)
        case err: IllegalArgumentException =>
          throw TypeError().ensureNodeInfo(node).initCause(err)
        case err: MatchError =>
          throw TypeError().ensureNodeInfo(node).initCause(err)

  lazy val builtinOperators
      : Map[String, PartialFunction[List[TLAValue], TLAValue]] =
    View[(TLABuiltinOperator, PartialFunction[List[TLAValue], TLAValue])](
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalAndSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) =>
          TLAValueBool(lhs && rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalOrSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) =>
          TLAValueBool(lhs || rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalNotSymbol) -> {
        case List(TLAValueBool(op)) => TLAValueBool(!op)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.ImpliesSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) =>
          TLAValueBool(!lhs || rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.EquivSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) =>
          TLAValueBool(lhs == rhs)
      },
      BuiltinModules.Intrinsics.memberAlpha("TRUE") -> { case Nil =>
        TLAValueBool(true)
      },
      BuiltinModules.Intrinsics.memberAlpha("FALSE") -> { case Nil =>
        TLAValueBool(false)
      },
      BuiltinModules.Intrinsics.memberAlpha("BOOLEAN") -> { case Nil =>
        TLAValueSet(Set(TLAValueBool(true), TLAValueBool(false)))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.EqualsSymbol) -> {
        case List(lhs, rhs) => TLAValueBool(lhs == rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.NotEqualsSymbol) -> {
        case List(lhs, rhs) => TLAValueBool(lhs != rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.InSymbol) -> {
        case List(lhs, TLAValueSet(rhs)) => TLAValueBool(rhs.contains(lhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.NotInSymbol) -> {
        case List(lhs, TLAValueSet(rhs)) => TLAValueBool(!rhs.contains(lhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.IntersectSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueSet(lhs & rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.UnionSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueSet(lhs | rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.SubsetOrEqualSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) =>
          TLAValueBool(lhs.subsetOf(rhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.BackslashSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) =>
          TLAValueSet(lhs.diff(rhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrefixUnionSymbol) -> {
        case List(TLAValueSet(set)) =>
          TLAValueSet(set.subsets().map(TLAValueSet.apply).toSet)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrefixUnionSymbol) -> {
        case List(TLAValueSet(set)) =>
          TLAValueSet(
            set.view
              .flatMap(valueFn { case TLAValueSet(memberSet) =>
                memberSet
              })
              .toSet,
          )
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.DomainSymbol) -> {
        case List(TLAValueFunction(fn)) => TLAValueSet(fn.keySet)
      },
      BuiltinModules.TLC.memberAlpha("Assert") -> {
        case List(TLAValueBool(cond), out) =>
          require(cond, out.toString)
          TLAValueBool(true)
      },
      BuiltinModules.TLC.memberSym(TLASymbol.ColonGreaterThanSymbol) -> {
        case List(lhs, rhs) => TLAValueFunction(Map(lhs -> rhs))
      },
      BuiltinModules.TLC.memberSym(TLASymbol.DoubleAtSignSymbol) -> {
        case List(TLAValueFunction(lhs), TLAValueFunction(rhs)) =>
          TLAValueFunction(lhs ++ rhs)
      },
      BuiltinModules.TLC.memberAlpha("SortSeq") -> { _ => throw Unsupported() },
      BuiltinModules.TLC.memberAlpha("ToString") -> {
        case List(value: TLAValue) =>
          TLAValueString(value.describe.linesIterator.mkString("\n"))
      },
      BuiltinModules.Sequences.memberAlpha("Seq") -> {
        case List(TLAValueSet(elems)) =>
          TLAValueSet(
            elems.toVector.permutations.map(TLAValueTuple.apply).toSet,
          )
      },
      BuiltinModules.Sequences.memberAlpha("Len") -> {
        case List(TLAValueTuple(elems)) => TLAValueNumber(elems.size)
      },
      BuiltinModules.Sequences.memberSym(TLASymbol.OSymbol) -> {
        case List(TLAValueTuple(lhs), TLAValueTuple(rhs)) =>
          TLAValueTuple(lhs ++ rhs)
      },
      BuiltinModules.Sequences.memberAlpha("Append") -> {
        case List(TLAValueTuple(elems), elem) => TLAValueTuple(elems :+ elem)
      },
      BuiltinModules.Sequences.memberAlpha("Head") -> {
        case List(TLAValueTuple(elems)) =>
          require(elems.nonEmpty)
          elems.head
      },
      BuiltinModules.Sequences.memberAlpha("Tail") -> {
        case List(TLAValueTuple(elems)) =>
          require(elems.nonEmpty)
          TLAValueTuple(elems.tail)
      },
      BuiltinModules.Sequences.memberAlpha("SubSeq") -> {
        case List(TLAValueTuple(_), TLAValueNumber(from), TLAValueNumber(to))
            if from > to =>
          TLAValueTuple(Vector.empty)
        case List(
              TLAValueTuple(elems),
              TLAValueNumber(from1),
              TLAValueNumber(to1),
            ) =>
          val from = from1 - 1
          val to = to1 - 1
          require(from >= 0 && to >= 0 && from < elems.size && to < elems.size)
          TLAValueTuple(elems.slice(from, to + 1))
      },
      BuiltinModules.Sequences.memberAlpha("SelectSeq") -> { _ =>
        throw Unsupported()
      },
      BuiltinModules.FiniteSets.memberAlpha("IsFiniteSet") -> {
        case List(TLAValueSet(_)) => TLAValueBool(true)
      },
      BuiltinModules.FiniteSets.memberAlpha("Cardinality") -> {
        case List(TLAValueSet(set)) => TLAValueNumber(set.size)
      },
      BuiltinModules.Peano.memberAlpha("Zero") -> { case Nil =>
        TLAValueNumber(0)
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.PlusSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueNumber(math.addExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.AsteriskSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueNumber(math.multiplyExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.LessThanOrEqualSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueBool(lhs <= rhs)
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.MinusSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueNumber(math.subtractExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.SlashSymbol) -> {
        case List(_, _) => throw Unsupported()
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.SuperscriptSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          // don't silently truncate overflows; fail with error
          val result = math.pow(lhs, rhs)
          require(result <= Int.MaxValue && result >= Int.MinValue)
          TLAValueNumber(result.toInt)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.GreaterThanOrEqualSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueBool(lhs >= rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.LessThanSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueBool(lhs < rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.GreaterThanSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          TLAValueBool(lhs > rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.DotDotSymbol) -> {
        case List(TLAValueNumber(from), TLAValueNumber(until)) =>
          TLAValueSet((from to until).view.map(TLAValueNumber.apply).toSet)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.DivSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          require(rhs != 0)
          TLAValueNumber(math.floorDiv(lhs, rhs))
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.PercentSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          require(rhs > 0)
          TLAValueNumber(math.floorMod(lhs, rhs))
      },
      BuiltinModules.Integers.memberSym(TLASymbol.NegationSymbol) -> {
        case List(TLAValueNumber(num)) => TLAValueNumber(-num)
      },
      BuiltinModules.Reals.memberAlpha("Real") -> { _ => throw Unsupported() },
    )
      .map: (op, impl) =>
        op.canonicalIdString -> impl
      .toMap

  final class Result[+V] private (private val value: Try[V]) extends AnyVal {
    override def toString: String = s"Result($value)"

    def assumeSuccess: V = value.get

    def outcomes: LazyList[Try[V]] = LazyList(value)

    private def transformErr(err: Throwable): Throwable = err match {
      case err: IllegalArgumentException => TypeError().initCause(err)
      case err: MatchError               => TypeError().initCause(err)
      case err                           => err
    }

    private def transformTryErr[T](t: Try[T]): Try[T] = t match {
      case Failure(err)   => Failure(transformErr(err))
      case s @ Success(_) => s
    }

    def map[U](fn: V => U): Result[U] =
      new Result(transformTryErr(value.map(fn)))

    def map[U](fn: PartialFunction[V, U]): Result[U] = map(fn.apply)

    def flatMap[U](fn: V => Result[U]): Result[U] =
      new Result(value match {
        case Failure(err)   => Failure(err)
        case Success(value) =>
          try {
            fn(value).value
          } catch {
            case NonFatal(err) =>
              Failure(transformErr(err))
          }
      })

    def flatMap[U](fn: PartialFunction[V, Result[U]]): Result[U] = flatMap(
      fn.apply,
    )

    def ensureNodeInfo(node: TLANode): Result[V] =
      new Result(value match {
        case Failure(err) =>
          err match {
            case err: TypeError   => Failure(err.ensureNodeInfo(node))
            case err: Unsupported => Failure(err.ensureNodeInfo(node))
            case err              => Failure(err)
          }
        case success: Success[V] => success
      })
  }

  object Result {
    def apply[V](v: => V): Result[V] = new Result(Try(v))
  }

  type Env = Map[String, TLAValue]

  private def allEnvChoices(
      bounds: List[TLAQuantifierBound],
      forceAll: Boolean = false,
  )(using
      env: Env,
  ): View[Env] =
    var hadEmpty = false
    val boundValues =
      bounds.view
        .map(_.set)
        .map(interpret)
        .map(_.narrowMatch { case TLAValueSet(set) => set })
        .tapEach(set => hadEmpty |= set.isEmpty)
        .takeWhile(_.nonEmpty || forceAll)
        .toList

    // short-circuit on empty
    if hadEmpty then return View.empty

    val assignmentGroups =
      bounds.view
        .flatMap:
          case TLAQuantifierBound(TLAQuantifierBound.IdsType, ids, set) =>
            val setValue = interpret(set).narrowMatch { case TLAValueSet(set) =>
              set
            }
            ids.view.map(id => id.id.id -> setValue)
          case TLAQuantifierBound(TLAQuantifierBound.TupleType, ids, set) =>
            val setValue = interpret(set).narrowMatch { case TLAValueSet(set) =>
              set
            }
            ids.view.zipWithIndex
              .map: (id, idx) =>
                id.id.id -> setValue.map: tpl =>
                  tpl.narrowMatch:
                    case TLAValueTuple(tpl) =>
                      require(tpl.size == ids.size)
                      tpl(idx)
        .toMap

    assignmentGroups
      .foldLeft(
        None: Option[View[Map[String, TLAValue]]],
      ):
        case (None, (id, set)) =>
          Some(set.view.map(v => env.updated(id, v)))
        case (Some(acc), (id, set)) =>
          Some(set.view.flatMap(v => acc.map(_.updated(id, v))))
      .get

  def interpret(expr: TLAExpression)(using
      env: Env,
  ): TLAValue = {
    expr.narrowMatch:
      case TLAString(value)    => TLAValueString(value)
      case TLANumber(value, _) =>
        value match {
          case TLANumber.IntValue(value) =>
            TLAValueNumber(value.intValue)
          case _ =>
            throw Unsupported().ensureHint(
              d"only int literals are supported",
            ) // TODO: support the other ones
        }
      case ident: TLAGeneralIdentifier =>
        env.get(ident.refersTo.canonicalIdString) match {
          case Some(value) =>
            value
          case None =>
            ident.refersTo match {
              case TLAOperatorDefinition(_, args, body, _) =>
                assert(args.isEmpty)
                interpret(body)
              case _ =>
                builtinOperators.get(ident.refersTo.canonicalIdString) match {
                  case Some(operator) =>
                    operator(Nil)
                  case None =>
                    throw Unsupported()
                      .ensureNodeInfo(ident)
                      .ensureHint(
                        d"can't process ${ident.refersTo.canonicalIdString}",
                      )
                }
            }
        }
      case TLADot(lhs, identifier) =>
        interpret(lhs).narrowMatch { case TLAValueFunction(value) =>
          val idx = TLAValueString(identifier.id)
          require(value.contains(idx))
          value(idx)
        }
      case TLACrossProduct(operands) =>
        operands.view
          .map(interpret)
          .map(_.narrowMatch { case TLAValueSet(set) => set })
          .foldLeft(None: Option[TLAValueSet]):
            case (None, set) =>
              Some(TLAValueSet(set.map(elem => TLAValueTuple(Vector(elem)))))
            case (Some(TLAValueSet(lhsSet)), rhsSet) =>
              Some:
                TLAValueSet:
                  lhsSet.flatMap:
                    case TLAValueTuple(lhsElems) =>
                      rhsSet.map(rhsElem => TLAValueTuple(lhsElems :+ rhsElem))
                    case _ => !!!
          .get
      case opcall @ TLAOperatorCall(_, _, arguments) =>
        opcall.refersTo match {
          // TLA+ LAMBDA and operator-like CONSTANT support
          case ref if env.contains(ref.canonicalIdString) =>
            env(ref.canonicalIdString).narrowMatch { case TLAValueLambda(fn) =>
              fn.applyOrElse(
                arguments.map(interpret),
                { (arguments: List[TLAValue]) =>
                  throw TypeError()
                    .ensureValueInfo(
                      TLAValueTuple(Vector.from(arguments)),
                    )
                    .ensureNodeInfo(opcall)
                },
              )
            }
          // 3 special cases implement short-circuiting boolean logic
          case ref
              if ref eq BuiltinModules.Intrinsics.memberSym(
                TLASymbol.LogicalAndSymbol,
              ) =>
            val List(lhs, rhs) = arguments
            interpret(lhs).narrowMatch {
              case TLAValueBool(true)  => interpret(rhs)
              case TLAValueBool(false) => TLAValueBool(false)
            }
          case ref
              if ref eq BuiltinModules.Intrinsics.memberSym(
                TLASymbol.LogicalOrSymbol,
              ) =>
            val List(lhs, rhs) = arguments
            interpret(lhs).narrowMatch {
              case TLAValueBool(true)  => TLAValueBool(true)
              case TLAValueBool(false) => interpret(rhs)
            }
          case ref
              if ref eq BuiltinModules.Intrinsics.memberSym(
                TLASymbol.ImpliesSymbol,
              ) =>
            val List(lhs, rhs) = arguments
            interpret(lhs).narrowMatch {
              case TLAValueBool(true)  => interpret(rhs)
              case TLAValueBool(false) => TLAValueBool(true)
            }
          case builtin
              if builtinOperators.contains(builtin.canonicalIdString) =>
            builtinOperators(builtin.canonicalIdString)(
              arguments.map(interpret),
            )
          case TLAOperatorDefinition(opName, args, body, _) =>
            require(
              args.size == arguments.size,
              s"arity mismatch (${opName.stringRepr})",
            )
            require(
              args.forall(_.variant.isInstanceOf[TLAOpDecl.NamedVariant]),
            )
            interpret(body)(using
              env ++ (args.view.map(_.canonicalIdString) `zip` arguments.view
                .map(
                  interpret,
                )),
            )
        }
      case TLAIf(cond, tval, fval) =>
        interpret(cond).narrowMatch { case TLAValueBool(value) =>
          if (value) interpret(tval) else interpret(fval)
        }
      case TLALet(defs, body) =>
        def impl(defs: List[TLAUnit])(using
            env: Map[String, TLAValue],
        ): TLAValue =
          defs match {
            case Nil               => interpret(body)
            case unit :: restUnits =>
              unit.narrowMatch {
                case defn @ TLAOperatorDefinition(_, args, body, _)
                    if args.isEmpty =>
                  interpret(body).narrowMatch { bodyVal =>
                    impl(restUnits)(using
                      env = env.updated(defn.canonicalIdString, bodyVal),
                    )
                  }
                case _: TLAOperatorDefinition =>
                  // for definitions with args, they will be called by TLAOperatorCall, and scoping is done already
                  impl(restUnits)
              }
          }

        impl(defs)
      case TLACase(arms, other) =>
        arms.view
          .map:
            case TLACaseArm(cond, result) =>
              interpret(cond).narrowMatch:
                case TLAValueBool(true) =>
                  Some(result)
                case TLAValueBool(false) =>
                  None
                case _ => throw TypeError().ensureNodeInfo(cond)
          .find(_.nonEmpty)
          .flatten
          .orElse(other)
          .map(interpret)
          .getOrElse(throw TypeError())
      case TLAFunction(args, body) =>
        val keySeq =
          args.view
            .flatMap:
              case TLAQuantifierBound(_, ids, _) => ids
            .toSeq
        val keyFn: (Env ?=> TLAValue) =
          if keySeq.size == 1
          then summon[Env](keySeq.head.canonicalIdString)
          else
            TLAValueTuple:
              keySeq.view
                .map: id =>
                  summon[Env](id.canonicalIdString)
                .toVector

        TLAValueFunction:
          allEnvChoices(args, forceAll = true)
            .map: env =>
              keyFn(using env) -> interpret(body)(using env)
            .toMap
      case TLAFunctionCall(function, params) =>
        val paramVal =
          params match
            case List(singleParam) => interpret(singleParam)
            case params => TLAValueTuple(params.view.map(interpret).toVector)

        interpret(function).narrowMatch {
          case TLAValueTuple(value) =>
            paramVal.narrowMatch {
              case TLAValueNumber(idx) if idx >= 1 && idx <= value.size =>
                value(idx - 1)
            }
          case TLAValueFunction(value) =>
            require(value.contains(paramVal))
            value(paramVal)
        }
      case TLAFunctionSet(from, to) =>
        val TLAValueSet(fromSet) = interpret(from): @unchecked
        val TLAValueSet(toSet) = interpret(to): @unchecked

        TLAValueSet {
          val keyList = fromSet.toList
          val valueList = toSet.toList
          val valueSets = keyList.iterator.foldLeft(
            Iterator.single(Nil: List[TLAValue]),
          ) { (acc, _) =>
            acc.flatMap(lst => valueList.iterator.map(v => v :: lst))
          }
          valueSets
            .map(valueSet => TLAValueFunction((keyList zip valueSet).toMap))
            .toSet
        }
      case TLAFunctionSubstitution(source, substitutions) =>
        substitutions.foldLeft(interpret(source)) { (fnValue, sub) =>
          val TLAFunctionSubstitutionPair(anchor, keys, value) = sub

          def subKeys(
              keys: List[TLAFunctionSubstitutionKey],
              origValue: TLAValue,
          ): TLAValue =
            keys match {
              case Nil =>
                interpret(value)(using
                  env.updated(anchor.canonicalIdString, origValue),
                )
              case TLAFunctionSubstitutionKey(indices) :: restKeys =>
                val indexValue = indices match
                  case List(index) => interpret(index)
                  case indices     =>
                    TLAValueTuple(indices.view.map(interpret).toVector)

                origValue.narrowMatch { case TLAValueFunction(origFn) =>
                  require(origFn.contains(indexValue))
                  val subValue = subKeys(restKeys, origFn(indexValue))
                  TLAValueFunction(origFn.updated(indexValue, subValue))
                }
            }

          subKeys(keys, fnValue)
        }
      case at @ TLAFunctionSubstitutionAt() =>
        env("@")
      case expr @ (TLAQuantifiedExistential(_, _) |
          TLAQuantifiedUniversal(_, _)) =>
        // merge universal and existential code paths, because they are so similar
        type CombineFn = View[Boolean] => Boolean
        val (bounds, body, combineFn) = expr.narrowMatch {
          case TLAQuantifiedUniversal(bounds, body) =>
            (bounds, body, (_.forall(identity)): CombineFn)
          case TLAQuantifiedExistential(bounds, body) =>
            (bounds, body, (_.exists(identity)): CombineFn)
        }

        val bools =
          allEnvChoices(bounds, forceAll = true)
            .map(interpret(body)(using _))
            .map(_.narrowMatch { case TLAValueBool(value) => value })

        TLAValueBool(combineFn(bools))
      case TLASetConstructor(contents) =>
        TLAValueSet(contents.view.map(interpret).toSet)
      case TLASetRefinement(TLAQuantifierBound(tpe, ids, set), when) =>
        val TLAValueSet(setValue) = interpret(set): @unchecked

        TLAValueSet:
          setValue
            .filter: elem =>
              tpe match
                case TLAQuantifierBound.IdsType =>
                  val List(id) = ids: @unchecked
                  interpret(when)(using env.updated(id.canonicalIdString, elem))
                    .narrowMatch:
                      case TLAValueBool(value) => value
                case TLAQuantifierBound.TupleType =>
                  elem.narrowMatch:
                    case TLAValueTuple(elems) if elems.size == ids.size =>
                      interpret(when)(using
                        env ++ (ids.view.map(_.canonicalIdString) `zip` elems),
                      ).narrowMatch:
                        case TLAValueBool(value) => value
      case TLASetComprehension(body, bounds) =>
        val envs = allEnvChoices(bounds)
        TLAValueSet(envs.map(interpret(body)(using _)).toSet)
      case TLATuple(elements) =>
        TLAValueTuple(elements.view.map(interpret).toVector)
      case TLARecordConstructor(fields) =>
        TLAValueFunction:
          fields.view
            .map:
              case TLARecordConstructorField(name, value) =>
                TLAValueString(name.id) -> interpret(value)
            .toMap
      case TLARecordSet(fields) =>
        TLAValueSet:
          fields
            .foldLeft(None: Option[Set[Map[TLAValue, TLAValue]]]):
              case (None, TLARecordSetField(name, set)) =>
                interpret(set).narrowMatch:
                  case TLAValueSet(set) =>
                    Some(Set(set.view.map(TLAValueString(name.id) -> _).toMap))
              case (Some(acc), TLARecordSetField(name, set)) =>
                interpret(set).narrowMatch:
                  case TLAValueSet(set) =>
                    Some:
                      acc.flatMap: accMap =>
                        set.view.map(v =>
                          accMap.updated(TLAValueString(name.id), v),
                        )
            .get
            .map(TLAValueFunction(_))
      case TLAQuantifiedChoose(TLAQuantifierBound(tpe, ids, set), body) =>
        val TLAValueSet(setValue) = interpret(set): @unchecked
        setValue
          .find: elem =>
            tpe match
              case TLAQuantifierBound.IdsType =>
                val List(id) = ids: @unchecked
                interpret(body)(using env.updated(id.canonicalIdString, elem))
                  .narrowMatch:
                    case TLAValueBool(value) => value
              case TLAQuantifierBound.TupleType =>
                elem.narrowMatch:
                  case TLAValueTuple(elems) if elems.size == ids.size =>
                    interpret(body)(using
                      env ++ (ids.view.map(_.canonicalIdString) `zip` elems),
                    ).narrowMatch:
                      case TLAValueBool(value) => value
          .getOrElse(throw TypeError().ensureNodeInfo(set))
  }
}
