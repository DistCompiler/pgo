package pgo.parser

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.TestingUtils
import pgo.model.mpcal.{ModularPlusCalInstance, ModularPlusCalMappingMacro}
import pgo.model.pcal.{PlusCalBuilder, PlusCalFairness, PlusCalMacro, PlusCalProcedure, PlusCalProcess, PlusCalStatement}
import pgo.model.tla.TLABuilder._
import pgo.model.pcal.PlusCalBuilder._
import pgo.model.mpcal.ModularPlusCalBuilder._
import pgo.model.tla.TLABuiltinModules

import java.util.Collections
import scala.jdk.CollectionConverters._

class ModularPlusCalUnitParserTest extends AnyFunSuite with ModularPlusCalParser with ParsingUtils {

  implicit def theContext: PCalParserContext = {
    val defns = TLABuiltinModules.Intrinsics.members ++
      TLABuiltinModules.Integers.members ++ TLABuiltinModules.Sequences.members ++
      List(id("global1"), id("global2"), id("global3"))

    implicit val ctx = defns.foldLeft(TLAParserContext())(_.withDefinition(_))
    PCalParserContext(archetypes = Map(
      "Archetype" -> archetype("Archetype", Nil.asJava, Nil.asJava, Nil.asJava),
      "Archetype3" -> archetype("Archetype3",
        List(
          PlusCalBuilder.pcalVarDecl("a", true, false, PLUSCAL_DEFAULT_INIT_VALUE),
          PlusCalBuilder.pcalVarDecl("b", true, false, PLUSCAL_DEFAULT_INIT_VALUE),
          PlusCalBuilder.pcalVarDecl("c", false, false, PLUSCAL_DEFAULT_INIT_VALUE)).asJava,
        Nil.asJava, Nil.asJava)))
  }

  def check[T](tag: String)(parser: Parser[T], input: String, expected: T)(implicit pos: Position): Unit =
    test(tag) {
      val path = ParserTestingUtils.ensureBackingFile(input)
      withClue(input) {
        val actual = checkResult {
          phrase(parser)(buildReader(path, input))
        }
        withClue("\n" + TestingUtils.stringDiff(expected.toString, actual.toString).mkString("\n")) {
          assert(actual == expected)
        }
      }
    }

  def checkMacro(tag: String)(pair: (String,PlusCalMacro))(implicit pos: Position): Unit =
    check(tag)(
      parser = mpcalWithRefs.pcalCSyntax.pcalMacro.cast,
      input = pair._1, expected = pair._2)

  checkMacro("simple macro") {
    """macro MyMacro(x) {
      |    x := x + 1;
      |}""".stripMargin ->
      `macro`("MyMacro", List("x").asJava,
        assign(idexp("x"), binop("+", idexp("x"), num(1))))
  }


  def checkProcedure(tag: String)(pair: (String,PlusCalProcedure))(implicit pos: Position): Unit =
    check(tag)(
      parser = mpcalWithRefs.pcalCSyntax.pcalProcedure.cast,
      input = pair._1, expected = pair._2)

  checkProcedure("simple procedure") {
    """procedure MyProcedure(x) {
      |    x := x + 1;
      |}""".stripMargin ->
      procedure("MyProcedure", List(
        PlusCalBuilder.pcalVarDecl("x", false, false, PLUSCAL_DEFAULT_INIT_VALUE)).asJava,
        Nil.asJava,
        assign(idexp("x"), binop("+", idexp("x"), num(1))))
  }

  checkProcedure("procedure with ref arg") {
    """procedure MyProcedure(ref x) {
      |    either { x := 10 } or { x := 20 };
      |}""".stripMargin ->
      procedure("MyProcedure", List(
        PlusCalBuilder.pcalVarDecl("x", true, false, PLUSCAL_DEFAULT_INIT_VALUE)).asJava,
        Nil.asJava,
        either(List(
          List[PlusCalStatement](assign(idexp("x"), num(10))).asJava,
          List[PlusCalStatement](assign(idexp("x"), num(20))).asJava,
        ).asJava))
  }

  checkProcedure("call proc with ref") {
    """procedure MyProcedure(ref x) {
      |    call MyProcedure(ref x);
      |}""".stripMargin ->
      procedure("MyProcedure",
        List(PlusCalBuilder.pcalVarDecl("x", true, false, PLUSCAL_DEFAULT_INIT_VALUE)).asJava,
        Nil.asJava,
        call("MyProcedure", ref("x")))
  }

  def checkProcess(tag: String)(pair: (String,PlusCalProcess))(implicit pos: Position): Unit =
    check(tag)(parser = mpcalWithRefs.pcalCSyntax.pcalProcess.cast,
      input = pair._1, expected = pair._2)

  checkProcess("ref in call in process") {
    """process (MyProcess = 12)
      |variables x;
      |{
      |    call MyProcedure(ref x);
      |}""".stripMargin ->
      process(
        PlusCalBuilder.pcalVarDecl("MyProcess", false, false, num(12)),
        PlusCalFairness.UNFAIR,
        List(
          PlusCalBuilder.pcalVarDecl("x", false, false, PLUSCAL_DEFAULT_INIT_VALUE)).asJava,
        call("MyProcedure", ref("x")))
  }

  // archetypes

  def checkInstance(tag: String)(pair: (String,ModularPlusCalInstance))(implicit pos: Position): Unit =
    check(tag)(parser = mpcalInstance, input = pair._1, expected = pair._2)

  checkInstance("simple instance") {
    """process (P \in 1..3) == instance Archetype();""".stripMargin ->
      instance(PlusCalBuilder.pcalVarDecl("P", false, true, binop("..", num(1), num(3))),
        PlusCalFairness.UNFAIR, "Archetype", Collections.emptyList(), Collections.emptyList())
  }

  checkInstance("weak fairness") {
    """fair process (P \in 1..3) == instance Archetype();""".stripMargin ->
      instance(PlusCalBuilder.pcalVarDecl("P", false, true, binop("..", num(1), num(3))),
        PlusCalFairness.WEAK_FAIR, "Archetype", Collections.emptyList(), Collections.emptyList())
  }

  checkInstance("strong fairness") {
    """fair+ process (P \in 1..3) == instance Archetype();""".stripMargin ->
      instance(PlusCalBuilder.pcalVarDecl("P", false, true, binop("..", num(1), num(3))),
        PlusCalFairness.STRONG_FAIR, "Archetype", Collections.emptyList(), Collections.emptyList())
  }

  checkInstance("full featured instance") {
    """process (P = "P") == instance Archetype3(ref global1, ref global2, global3)
      |  mapping global1 via MappingMacro1
      |  mapping global2[_] via MappingMacro2;""".stripMargin ->
      instance(PlusCalBuilder.pcalVarDecl("P", false, false, str("P")),
        PlusCalFairness.UNFAIR,
        "Archetype3",
        List(
          ref("global1"),
          ref("global2"),
          idexp("global3")).asJava,
        List(
          mapping("global1", false, "MappingMacro1"),
          mapping("global2", true, "MappingMacro2")).asJava)
  }

  checkInstance("instance with indexed mappings") {
    """process (P = "P") == instance Archetype3(ref global1, 42, global3)
      |  mapping @2 via MappingMacro1
      |  mapping @3[_] via MappingMacro2;""".stripMargin ->
      instance(PlusCalBuilder.pcalVarDecl("P", false, false, str("P")),
        PlusCalFairness.UNFAIR,
        "Archetype3",
        List(
          ref("global1"),
          num(42),
          idexp("global3")).asJava,
        List(
          mapping(2, false, "MappingMacro1"),
          mapping(3, true, "MappingMacro2")).asJava)
  }

  def checkMappingMacro(tag: String)(pair: (String, ModularPlusCalMappingMacro))(implicit pos: Position): Unit =
    check(tag)(parser = mpcalMappingMacro, input = pair._1, expected = pair._2)

  checkMappingMacro("simple mapping macro") {
    """mapping macro MappingMacro {
      |  read {
      |    yield $value;
      |  }
      |  write {
      |    yield $value;
      |  }
      |}""".stripMargin ->
      mappingMacro("MappingMacro",
        Collections.singletonList(`yield`(DOLLAR_VALUE)),
        Collections.singletonList(`yield`(DOLLAR_VALUE)))
  }

  checkMappingMacro("mapping macro with either") {
    """mapping macro UnreliableCounter {
      |  read {
      |    yield $value;
      |  }
      |  write {
      |    either {
      |      yield $variable + $value;
      |    } or {
      |      yield $variable;
      |    }
      |  }
      |}""".stripMargin ->
      mappingMacro("UnreliableCounter",
        Collections.singletonList(`yield`(DOLLAR_VALUE)),
        Collections.singletonList(
          either(
            List(
              List[PlusCalStatement](
                `yield`(binop("+", DOLLAR_VARIABLE, DOLLAR_VALUE))).asJava,
              List[PlusCalStatement](
                `yield`(DOLLAR_VARIABLE)).asJava).asJava)))
  }

  checkMappingMacro("mapping macro with multiple statements") {
    """mapping macro MappingMacro {
      |  read {
      |    await "someSpecialCondition";
      |    yield $value;
      |  }
      |  write {
      |    yield $value;
      |  }
      |}""".stripMargin ->
      mappingMacro("MappingMacro",
        List(
          await(str("someSpecialCondition")),
          `yield`(DOLLAR_VALUE)).asJava,
        List[PlusCalStatement](`yield`(DOLLAR_VALUE)).asJava)
  }

  checkMappingMacro("lossy network model") {
    """mapping macro LossyNetwork {
      |		read {
      |			await Len($variable) > 0;
      |			with (msg = Head($variable)) {
      |		    	$variable := Tail($variable);
      |		    	yield msg;
      |			}
      |		}
      |
      |		write {
      |			either {
      |				yield $variable;
      |			} or {
      |				await Len($variable) < global1;
      |				yield Append($variable, $value);
      |			}
      |		}
      |}""".stripMargin ->
      mappingMacro(
        "LossyNetwork",
        List(
          await(binop(">", opcall("Len", DOLLAR_VARIABLE), num(0))),
          `with`(
            List(
              PlusCalBuilder.pcalVarDecl("msg", false, false, opcall("Head", DOLLAR_VARIABLE))).asJava,
            assign(DOLLAR_VARIABLE, opcall("Tail", DOLLAR_VARIABLE)),
            `yield`(idexp("msg")))).asJava,
        List[PlusCalStatement](
          either(List(
            List[PlusCalStatement](`yield`(DOLLAR_VARIABLE)).asJava,
            List[PlusCalStatement](
              await(binop("<", opcall("Len", DOLLAR_VARIABLE), idexp("global1"))),
              `yield`(opcall("Append", DOLLAR_VARIABLE, DOLLAR_VALUE))).asJava).asJava)).asJava)
  }
}
