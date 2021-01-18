package pgo.trans.passes.validation

import org.scalatest.funsuite.AnyFunSuite
import pgo.TestingUtils
import pgo.errors.{Issue, TopLevelIssueContext}
import pgo.model.pcal.PlusCalBuilder._
import pgo.model.tla.TLABuilder._

import java.util.Collections
import scala.jdk.CollectionConverters._

class ValidationPassTest extends AnyFunSuite {
  def check(tag: String)(pair: (String,List[Issue])): Unit =
    test(tag) {
      val (specStr, expectedIssues) = pair
      val ctx = new TopLevelIssueContext()

      val (_, _, spec) = TestingUtils.parseMPCalFromString(specStr)

      ValidationPass.perform(ctx, spec)

      assert(ctx.getIssues.asScala.toList == expectedIssues)
    }

  check("no issues") {
    """
      |---- MODULE NoIssues ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal NoIssues {
      |	 procedure MyProcedure(y) {
      |		 l2: print(3 - 3);
      |			 if (TRUE) {
      |				 y := 20;
      |			 } else {
      |				 y := 10;
      |			 }
      |	 }
      |
      |  archetype MyArchetype(ref x) {
      |		 l1: print(1 + 1);
      |		 l2: either { x := 10 } or { x := 20 };
      |	 }
      |
      |	 process (MyProcess = 32) {
      |		 l3: print(2 * 2);
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> Nil
  }

  check("archetype no first label") {
    """
      |---- MODULE ArchetypeNoFirstLabel ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal ArchetypeNoFirstLabel {
      |	 archetype MyArchetype() {
      |		 print(1 + 1);
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new MissingLabelIssue(printS(binop("+", num(1), num(1)))))
  }

  check("procedure no first label") {
    """
      |---- MODULE ProcedureNoFirstLabel ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal ProcedureNoFirstLabel {
      |	 procedure MyProcess() {
      |		 print(1 + 1);
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new MissingLabelIssue(printS(binop("+", num(1), num(1)))))
  }

  check("process no first label") {
    """
      |---- MODULE ArchetypeNoFirstLabel ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal ProcessNoFirstLabel {
      |	 process (MyProcess = 32) {
      |		 print(1 + 1);
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new MissingLabelIssue(printS(binop("+", num(1), num(1)))))
  }

  check("more than one issue") {
    """
      |---- MODULE MoreThanOneIssue ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal MoreThanOneIssue {
      |
      |	 procedure ValidProcedure() {
      |		 l2: print(3 - 3);
      |	 }
      |
      |	 procedure InvalidProcedure() {
      |		 print("invalid procedure!");
      |	 }
      |
      |  archetype ValidArchetype() {
      |		 l1: print(1 + 1);
      |	 }
      |
      |	 archetype InvalidArchetype() {
      |		 print("invalid archetype!");
      |	 }
      |
      |	 process (ValidProcess = 32) {
      |		 l3: print(2 * 2);
      |	 }
      |
      |	 process (InvalidProcess = 64) {
      |		 print("invalid process!");
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new MissingLabelIssue(printS(str("invalid archetype!"))),
      new MissingLabelIssue(printS(str("invalid procedure!"))),
      new MissingLabelIssue(printS(str("invalid process!"))))
  }

  check("while labels") {
    """
      |---- MODULE WhileLabels ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal WhileLabels {
      |	 procedure CorrectProcedure() {
      |		 l2: print "procedure";
      |		 l3: while (FALSE) { print(3 - 3) }; (* all good *)
      |	 }
      |
      |  archetype IncorrectArchetype() {
      |		 l1: print "first label";
      |		 while (TRUE) { print "hello" }; (* missing label here *)
      |	 }
      |
      |	 process (IncorrectProcess = 32) {
      |		 while (10 < 20) { print(2 * 2) }; (* missing label (first statement) *)
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new MissingLabelIssue(
        whileS(
          bool(true),
          Collections.singletonList(printS(str("hello"))))),
      new MissingLabelIssue(
        whileS(
          binop("<", num(10), num(20)),
          Collections.singletonList(printS(binop("*", num(2), num(2)))))))
  }

  check("call labeling rules") {
    """
      |---- MODULE CallLabelingRules ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal CallLabelingRules {
      |	 procedure MyProcedure() {
      |		 l2: print "procedure";
      |		 call SomeProcedure();
      |		 return; (* no label required *)
      |	 }
      |
      |  archetype MyArchetype() {
      |		 l1: print "first label";
      |		 call MyProcedure();
      |		 call MyProcedure(); (* missing label *)
      |	 }
      |
      |	 process (MyProcess = 32)
      |  variables x;
      |  {
      |		 l3: print "process";
      |		 call MyProcedure();
      |		 goto l3; (* no label required *)
      |		 l4: print "next label";
      |		 call MyProcedure();
      |		 x := 10; (* missing label *)
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new MissingLabelIssue(call("MyProcedure")),
      new MissingLabelIssue(assign(idexp("x"), num(10))))
  }

  check("return goto labeling rules") {
    """
      |---- MODULE ReturnGotoLabelingRules ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal ReturnGotoLabelingRules {
      |
      |	 procedure MyProcedure() {
      |		 l2: print "procedure";
      |		 return;
      |		 goto l2; (* missing label *)
      |	 }
      |
      |  archetype MyArchetype() {
      |		 l1: print "first label";
      |		 goto l1;
      |		 print "needs label"; (* missing label *)
      |	 }
      |
      |	 process (MyProcess = 32)
      |  variables x;
      |  {
      |		 l3: print "process";
      |		 goto l3;
      |		 x := 10; (* missing label *)
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new MissingLabelIssue(printS(str("needs label"))),
      new MissingLabelIssue(gotoS("l2")),
      new MissingLabelIssue(assign(idexp("x"), num(10))))
  }

  check("if either labeling rules") {
    """
      |---- MODULE IfEitherLabelingRules ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal IfEitherLabelingRules {
      |
      |	 procedure MyProcedure()
      |  variables v;
      |  {
      |		 l2: print "procedure";
      |		 either { v := 10 } or { return };
      |		 goto l2; (* missing label *)
      |	 }
      |
      |  archetype MyArchetype() {
      |		 l1: print "first label";
      |		 if (TRUE) {
      |			 print "true";
      |		 } else if (TRUE) {
      |			 call MyProcedure();
      |		 };
      |
      |		 print "needs label"; (* missing label *)
      |	 }
      |
      |	 process (MyProcess = 32)
      |  variables x, y;
      |  {
      |		 l3: print "process";
      |		 either { x := 0 } or { goto l3 };
      |		 l4: print "all good";
      |
      |		 either { goto l4 } or { skip };
      |		 x := 50; (* missing label *)
      |
      |		 l5: if (TRUE) {
      |				 l6: print "label";
      |			 };
      |		 y := 20; (* missing label *)
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new MissingLabelIssue(printS(str("needs label"))),
      new MissingLabelIssue(gotoS("l2")),
      new MissingLabelIssue(assign(idexp("x"), num(50))),
      new MissingLabelIssue(assign(idexp("y"), num(20))))
  }

  check("macro rules") {
    """
      |---- MODULE MacroRules ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal MacroRules {
      |	 macro ValidMacro() {
      |		 print(1 + 1);
      |		 skip; \* x := 10; \* TODO: how to scope macros?
      |	 }
      |
      |	 macro InvalidMacro() {
      |		 either { skip } or { l1: print(10) }; (* invalid *)
      |		 l2: print(20); (* invalid *)
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new LabelNotAllowedIssue(labeled(label("l1"), printS(num(10)))),
      new LabelNotAllowedIssue(labeled(label("l2"), printS(num(20)))))
  }

  check("with rules") {
    """
      |---- MODULE WithRules ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal WithRules {
      |	 macro MacroWith() {
      |		 print(1 + 1);
      |		 with (x = 10) {
      |			 print x;
      |			 m1: x := 20; (* invalid *)
      |		 };
      |		 m2: print(20); (* invalid *)
      |	 }
      |
      |	 procedure ProcedureWith() {
      |		 l1: with (x = 10) {
      |				 l2: print x; (* invalid *)
      |			 }
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new LabelNotAllowedIssue(labeled(label("m1"), assign(idexp("x"), num(20)))),
      new LabelNotAllowedIssue(labeled(label("m2"), printS(num(20)))),
      new LabelNotAllowedIssue(labeled(label("l2"), printS(idexp("x")))))
  }

  check("assignment rules") {
    """
      |---- MODULE AssignmentRules ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal AssignmentRules {
      |
      |	 procedure MyProcedure(x, y)
      |  variables x, y;
      |  {
      |		 p: either { y := 10 } or { skip };
      |			y := 11; (* missing label *)
      |		 p2: y := 20;
      |			 x := y || y := x; (* swap x and y: invalid *)
      |	 }
      |
      |  archetype MyArchetype(ref x)
      |  variables x;
      |  {
      |		 a1: x := 10;
      |		 x := 11; (* missing label *)
      |	 }
      |
      |	 process (MyProcess = 23)
      |  variables n;
      |  {
      |		 l1: n := 2;
      |		 l2: while (n < 10) {
      |			 n := 12;
      |			 if (n = 20) {
      |				 n := 100; (* missing label *)
      |			 }
      |		 };
      |		 n := 32; (* label not missing *)
      |
      |		 l3: if (n = 32) {
      |			 n := 0;
      |		 };
      |		 n := 12; (* missing label *)
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new MissingLabelIssue(assign(idexp("x"), num(11))),
      new MissingLabelIssue(assign(idexp("y"), num(11))),
      new MissingLabelIssue(assign(idexp("x"), idexp("y"), idexp("y"), idexp("x"))),
      new MissingLabelIssue(assign(idexp("n"), num(100))),
      new MissingLabelIssue(assign(idexp("n"), num(12))))
  }

  check("reserved labels") {
    """
      |---- MODULE ReservedLabels ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal ReservedLabels {
      |	 procedure MyProcedure(y) {
      |		 p: either { p1: y := 20 } or { Error: skip }; (* reserved *)
      |	 }
      |
      |  archetype MyArchetype(ref x) {
      |		 Done: x := 10; (* reserved *)
      |		 done: x := 30; (* no problem *)
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new ReservedLabelNameIssue(labeled(label("Done"), assign(idexp("x"), num(10)))),
      new ReservedLabelNameIssue(labeled(label("Error"), skip())))
  }

  check("mapping with labels") {
    """
      |---- MODULE MappingWithLabels ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal MappingWithLabels {
      |	 mapping macro ContainsLabels {
      |		   read {
      |          r: yield $variable
      |      }
      |      write {
      |          if ($variable > 10) {
      |              w: yield $value;
      |          }
      |      }
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new StatementNotAllowedIssue(labeled(label("r"), `yield`(DOLLAR_VARIABLE))),
      new StatementNotAllowedIssue(labeled(label("w"), `yield`(DOLLAR_VALUE))))
  }

  check("mapping macro with call goto") {
    """
      |---- MODULE MappingMacroWithCallGoto ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal MappingMacroWithCallGoto {
      |	 mapping macro InvalidStatements {
      |		 read {
      |          await Len($variable) = 0;
      |          if (TRUE) {
      |              call YesProcedure();
      |          };
      |          call NoProcedure();
      |          yield 0;
      |      }
      |      write {
      |          either { yield $value }
      |          or     { goto l1 };
      |      }
      |	 }
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new StatementNotAllowedIssue(call("YesProcedure")),
      new StatementNotAllowedIssue(call("NoProcedure")),
      new StatementNotAllowedIssue(gotoS("l1")))
  }

}
