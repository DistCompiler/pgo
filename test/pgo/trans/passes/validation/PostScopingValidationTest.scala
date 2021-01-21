package pgo.trans.passes.validation

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.TestingUtils
import pgo.errors.{Issue, TopLevelIssueContext}
import pgo.model.mpcal.ModularPlusCalBuilder._
import pgo.model.mpcal.ModularPlusCalUtils
import pgo.model.pcal.PlusCalBuilder._
import pgo.model.pcal._
import pgo.model.tla.TLABuilder._
import pgo.trans.intermediate.{DefinitionRegistry, TLABuiltins}

import java.util.Collections
import scala.jdk.CollectionConverters._

class PostScopingValidationTest extends AnyFunSuite {
  def check(tag: String)(pair: (String,List[Issue]))(implicit pos: Position): Unit =
    test(tag) {
      val (specStr, expectedIssues) = pair

      val (_, _, spec) = TestingUtils.parseMPCalFromString(specStr)

      val ctx = new TopLevelIssueContext()

      val registry = new DefinitionRegistry
      TLABuiltins.fillDefinitionRegistry(registry)
      ModularPlusCalUtils.fillDefinitionRegistryFromModularPlusCalBlock(registry, spec)

      ValidationPass.perform(ctx, spec)
      assert(!ctx.hasErrors)

      ValidationPass.performPostScoping(ctx, registry, spec)
      assert(ctx.getIssues.asScala.toList == expectedIssues)
    }

  check("inconsistent instantiations") {
    """
       |---- MODULE InconsistentInstantiations ----
       |EXTENDS Sequences, FiniteSets, Integers
       |(*
       |--mpcal InconsistentInstantiations {
       |   mapping macro MyMapping {
       |     read {
       |       yield "";
       |     }
       |     write {
       |       yield "";
       |     }
       |   }
       |   mapping macro OtherMapping {
       |     read {
       |       yield "";
       |     }
       |     write {
       |       yield "";
       |     }
       |   }
       |   mapping macro SomeMapping {
       |     read {
       |       yield "";
       |     }
       |     write {
       |       yield "";
       |     }
       |   }
       |   archetype A1(ref a1) {
       |     l1:
       |        print 1;
       |   }
       |   archetype A2(ref a2) {
       |     l2:
       |        print 2;
       |   }
       |   variables network = <<>>;
       |   fair process (P1 = 1) == instance A1(ref network)
       |       mapping network[_] via MyMapping;
       |   fair process (Other = 42) == instance A2(ref network);
       |   fair process (P2 = 2) == instance A1(ref network)     \* conflicts with P1
       |       mapping network via OtherMapping;
       |   fair process (P3 = 3) == instance A1(network);        \* conflicts with P1
       |   fair process (Other2 = 24) == instance A2(network)    \* conflicts with Other
       |       mapping network[_] via SomeMapping;
       | }
       | *)
       |\* BEGIN TRANSLATION
       |====
       |""".stripMargin -> List(
      new InconsistentInstantiationIssue(
        instance(
          pcalVarDecl("P2", false, false, num(2)),
          PlusCalFairness.WEAK_FAIR,
          "A1",
          Collections.singletonList(ref("network")),
          Collections.singletonList(
            mapping("network", false, "OtherMapping"))),
        instance(
          pcalVarDecl("P1", false, false, num(1)),
          PlusCalFairness.WEAK_FAIR,
          "A1",
          Collections.singletonList(ref("network")),
          Collections.singletonList(mapping("network", true, "MyMapping")))),
      new InconsistentInstantiationIssue(
        instance(
          pcalVarDecl("P3", false, false, num(3)),
          PlusCalFairness.WEAK_FAIR,
          "A1",
          Collections.singletonList(idexp("network")),
          Collections.emptyList),
        instance(
          pcalVarDecl("P1", false, false, num(1)),
          PlusCalFairness.WEAK_FAIR,
          "A1",
          Collections.singletonList(ref("network")),
          Collections.singletonList(mapping("network", true, "MyMapping")))),
      new InconsistentInstantiationIssue(
        instance(
          pcalVarDecl("Other2", false, false, num(24)),
          PlusCalFairness.WEAK_FAIR,
          "A2",
          Collections.singletonList(idexp("network")),
          Collections.singletonList(mapping("network", true, "SomeMapping"))),
        instance(
          pcalVarDecl("Other", false, false, num(42)),
          PlusCalFairness.WEAK_FAIR,
          "A2",
          Collections.singletonList(ref("network")),
          Collections.emptyList)))
  }

  check("multiple mapping") {
    """
      |---- MODULE MultipleMapping ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal MultipleMapping {
      |  mapping macro Macro {
      |    read {
      |      yield "";
      |    }
      |    write {
      |      yield "";
      |    }
      |  }
      |  archetype A(ref a) {
      |    l1:
      |      print 1;
      |  }
      |  variables global = <<>>;
      |  process (P = 1) == instance A(ref global)
      |      mapping global[_] via Macro;
      |  process (Q = 2) == instance A(ref global)
      |      mapping @1 via Macro;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |""".stripMargin -> List(
      new InconsistentInstantiationIssue(
        instance(
          pcalVarDecl("Q", false, false, num(2)),
          PlusCalFairness.UNFAIR,
          "A",
          Collections.singletonList(ref("global")),
          Collections.singletonList(mapping(1, false, "Macro"))),
        instance(pcalVarDecl("P", false, false, num(1)),
          PlusCalFairness.UNFAIR,
          "A",
          Collections.singletonList(ref("global")),
          Collections.singletonList(mapping("global", true, "Macro")))))
  }

  check("invalid assignments") {
    """
      |---- MODULE InvalidAssignments ----
      |EXTENDS Sequences, FiniteSets, Integers
      |(*
      |--mpcal InvalidAssignments {
      |     mapping macro SomeMacro {
      |       read {
      |         yield "";
      |       }
      |       write {
      |         yield "";
      |       }
      |     }
      |
      |     mapping macro OtherMacro {
      |       read {
      |         yield "";
      |       }
      |       write {
      |         yield "";
      |       }
      |     }
      |
      |     archetype MyArchetype(ref nonMapped, ref varMapped, ref fnMapped)
      |       variables someLocal;
      |     {
      |         l1:
      |           while (TRUE) {
      |               nonMapped := 10;                  \* valid
      |               someLocal := fnMapped[nonMapped]; \* valid
      |           };
      |
      |         l2:
      |           either { varMapped[10] := 0; }  \* invalid
      |           or     { varMapped := 10;    }; \* valid
      |
      |         l3:
      |           if (varMapped[10] = 10) {       \* invalid
      |               someLocal := varMapped[10]; \* invalid
      |           } else {
      |               nonMapped[30] := 20;        \* valid
      |               fnMapped := 12;             \* invalid
      |           }
      |     }
      |
      |     variables n = 0, v = 0, f = <<0>>;
      |
      |     process (P1 = 42) == instance MyArchetype(ref n, ref v, ref f)
      |         mapping v via SomeMacro
      |         mapping f[_] via OtherMacro;
      | }
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin -> List(
      new InvalidArchetypeResourceUsageIssue(
        assign(fncall(idexp("varMapped"), num(10)), num(0)),
        false),
      new InvalidArchetypeResourceUsageIssue(
        ifS(
          binop("=", fncall(idexp("varMapped"), num(10)), num(10)),
          List[PlusCalStatement](
            assign(idexp("someLocal"), fncall(idexp("varMapped"), num(10)))).asJava,
          List[PlusCalStatement](
            assign(fncall(idexp("nonMapped"), num(30)), num(20)),
            assign(idexp("fnMapped"), num(12))).asJava),
         false),
      new InvalidArchetypeResourceUsageIssue(
        assign(idexp("someLocal"), fncall(idexp("varMapped"), num(10))),
        false),
      new InvalidArchetypeResourceUsageIssue(
        assign(fncall(idexp("nonMapped"), num(30)), num(20)),
        false),
      new InvalidArchetypeResourceUsageIssue(
        assign(idexp("fnMapped"), num(12)),
        true))
  }

}
