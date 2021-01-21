package pgo

import com.github.difflib.{DiffUtils, UnifiedDiffUtils}
import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.errors.TopLevelIssueContext
import pgo.model.pcal.{PlusCalAlgorithm, PlusCalFairness}
import pgo.model.pcal.PlusCalBuilder.{`with`, _}
import pgo.model.tla.TLABuilder._

import java.util
import java.util.{Arrays, Collections}
import scala.jdk.CollectionConverters._

class PlusCalCodeGenPassTest extends AnyFunSuite {
  def check(tag: String)(pair: (String, PlusCalAlgorithm))(implicit pos: Position): Unit =
    test(tag) {
      val (inputStr, expectedAlgorithm) = pair
      withClue(s"with input:\n$inputStr\n") {
        val (testFile, tlaModule, mpcalBlock) = TestingUtils.parseMPCalFromString(inputStr)

        val main = new PGoMain(Array[String]())
        val ctx = new TopLevelIssueContext()

        val actualAlgorithm = main.mpcalToPcal(testFile, ctx, mpcalBlock, tlaModule)

        withClue(s"with diff:\n${TestingUtils.stringDiff(expected = expectedAlgorithm.toString, actual = actualAlgorithm.toString).mkString("\n")}\n") {
          assert(expectedAlgorithm == actualAlgorithm)
        }
      }
    }

  check("algorithm1") {
    """
      |----MODULE Algorithm1 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm1 {
      |    archetype A1(a) {
      |        l1: skip;
      |    }
      |
      |    variable x = 10;
      |    fair process (P1 = 42) == instance A1(x);
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // -- algorithm Algorithm1 {
      //     variable x = 10;
      //     fair process (P1 = 42) {
      //         l1: skip;
      //     }
      // }
      algorithm(
        "Algorithm1",
        Collections.singletonList(pcalVarDecl("x", false, false, num(10))),
        Collections.emptyList,
        Collections.emptyList,
        Collections.emptyList,
        process(
          pcalVarDecl("P1", false, false, num(42)),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList,
          labeled(label("l1"),
            skip)))
  }

  check("algorithm2") {
    """
      |----MODULE Algorithm2 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm2 {
      |    mapping macro Zero {
      |        read {
      |            yield 0
      |        }
      |        write {
      |            yield $variable
      |        }
      |    }
      |    archetype A1(a, ref b) {
      |        l1: print << a, b >>;
      |    }
      |
      |    variables x = 10, y = 20;
      |    fair process (P1 = 42) == instance A1(x, ref y)
      |    mapping x via Zero;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm2 {
      //     variables x = 10, y = 20, aRead, bRead;
      //     fair process (P1 = 42)
      //     {
      //         l1: aRead := 0;
      //             bRead := y;
      //             print << (aRead), (bRead) >>;
      //     }
      // }
      algorithm(
        "Algorithm2",
        util.Arrays.asList(
          pcalVarDecl("x", false, false, num(10)),
          pcalVarDecl("y", false, false, num(20)),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("bRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList,
        Collections.emptyList,
        Collections.emptyList,
        process(
          pcalVarDecl("P1", false, false, num(42)),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList,
          labeled(label("l1"),
            assign(idexp("aRead"), num(0)),
            assign(idexp("bRead"), idexp("y")),
            printS(tuple(idexp("aRead"), idexp("bRead"))))))
  }

  check("algorithm3") {
    """
      |----MODULE Algorithm3 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm3 {
      |   mapping macro WeirdMacro {
      |       read {
      |           $variable := $variable - 1;
      |           with (v = 50) {
      |               either { yield v } or { yield 10 }
      |           }
      |       }
      |       write {
      |           yield $value + 1
      |       }
      |   }
      |   archetype A1(ref a, b)
      |   variable local; {
      |       l1: if (a >= 42) {
      |               local := 42;
      |           };
      |       l2: a := 10;
      |       l3: local := a + b;
      |       l4: print local;
      |   }
      |   variables x = 10, y = 20;
      |   fair process (P1 = 100) == instance A1(ref x, y)
      |   mapping x via WeirdMacro;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm3 {
      //    variables x = 10, y = 20, aRead, aWrite, bRead;
      //    process (P1 = 100)
      //    variables local;
      //    {
      //        l1:
      //            aWrite := (x)-(1);
      //            with (v0 = 50) {
      //                either {
      //                    aRead := v0;
      //                } or {
      //                    aRead := 10;
      //                };
      //            };
      //            if ((aRead)>=(42)) {
      //                local := 42;
      //                x := aWrite;
      //            } else {
      //                x := aWrite;
      //            }
      //        l2:
      //            aWrite := (10)+(1);
      //            x := aWrite;
      //        l3:
      //            aWrite := (x)-(1);
      //            with (v1 = 50) {
      //                either {
      //                    aRead := v1;
      //                } or {
      //                    aRead := 10;
      //                };
      //            };
      //            bRead := y;
      //            local := (aRead)+(bRead);
      //            x := aWrite;
      //        l4:
      //            print local;
      //
      //    }
      // }
      algorithm(
        "Algorithm3",
        util.Arrays.asList(
          pcalVarDecl("x", false, false, num(10)),
          pcalVarDecl("y", false, false, num(20)),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("bRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList,
        Collections.emptyList,
        Collections.emptyList,
        process(
          pcalVarDecl("P1", false, false, num(100)),
          PlusCalFairness.WEAK_FAIR,
          Collections.singletonList(
            pcalVarDecl("local", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
          labeled(label("l1"),
            assign(idexp("aWrite"), binop("-", idexp("x"), num(1))),
            `with`(
              Collections.singletonList(pcalVarDecl("v0", false, false, num(50))),
              either(util.Arrays.asList(
                Collections.singletonList(assign(idexp("aRead"), idexp("v0"))),
                Collections.singletonList(assign(idexp("aRead"), num(10)))))),
            ifS(
              binop(">=", idexp("aRead"), num(42)),
              util.Arrays.asList(
                assign(idexp("local"), num(42)),
                assign(idexp("x"), idexp("aWrite"))),
              Collections.singletonList(assign(idexp("x"), idexp("aWrite"))))),
          labeled(label("l2"),
            assign(idexp("aWrite"), binop("+", num(10), num(1))),
            assign(idexp("x"), idexp("aWrite"))), labeled(label("l3"),
            assign(idexp("aWrite"), binop("-", idexp("x"), num(1))),
            `with`(
              Collections.singletonList(pcalVarDecl("v1", false, false, num(50))),
              either(util.Arrays.asList(
                Collections.singletonList(assign(idexp("aRead"), idexp("v1"))),
                Collections.singletonList(assign(idexp("aRead"), num(10)))))),
            assign(idexp("bRead"), idexp("y")),
            assign(idexp("local"), binop("+", idexp("aRead"), idexp("bRead"))),
            assign(idexp("x"), idexp("aWrite"))), labeled(label("l4"),
            printS(idexp("local")))))
  }

  check("algorithm4") {
    """
      |----MODULE Algorithm4 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm4 {
      |    mapping macro WeirdMacro {
      |        read {
      |            $variable := $variable - 1;
      |            yield $variable;
      |        }
      |        write {
      |            $variable := $variable + 1;
      |            yield $variable + $value;
      |        }
      |    }
      |    archetype A1(ref a, b)
      |    variable local; {
      |        l1: if (a >= 42) {
      |                a := 42;
      |            };
      |        l2: a := 10;
      |            local := a + a + b;
      |        l3: local := a + b;
      |        l4: print local;
      |    }
      |    variables x = 10, y = 20;
      |    fair process (P1 = 100) == instance A1(ref x, y)
      |    mapping x via WeirdMacro;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm4 {
      //     variables x = 10, y = 20, aRead, aWrite, aWrite0, aWrite1, aRead0, bRead;
      //     process (P1 = 100)
      //     variables local;
      //     {
      //         l1:
      //             aWrite := (x)-(1);
      //             aRead := aWrite;
      //             if ((aRead)>=(42)) {
      //                 aWrite0 := (aWrite)+(1);
      //                 aWrite1 := (aWrite0)+(42);
      //                 aWrite2 := aWrite1;
      //                 x := aWrite2;
      //             } else {
      //                 aWrite2 := x;
      //                 x := aWrite2;
      //             };
      //         l2:
      //             aWrite := (x)+(1);
      //             aWrite0 := (aWrite)+(10);
      //             aWrite0 := (aWrite0)-(1);
      //             aRead := aWrite0;
      //             aWrite1 := (aWrite0)-(1);
      //             aRead0 := aWrite1;
      //             bRead := y;
      //             local := ((aRead)+(aRead0))+(bRead);
      //             x := aWrite1;
      //         l3:
      //             aWrite := (x)-(1);
      //             aRead := aWrite;
      //             bRead := y;
      //             local := (aRead)+(bRead);
      //             x := aWrite;
      //         l4:
      //             print local;
      //     }
      // }
      algorithm(
        "Algorithm4",
        util.Arrays.asList(
          pcalVarDecl("x", false, false, num(10)),
          pcalVarDecl("y", false, false, num(20)),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite2", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("bRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList,
        Collections.emptyList,
        Collections.emptyList,
        process(
          pcalVarDecl("P1", false, false, num(100)),
          PlusCalFairness.WEAK_FAIR,
          Collections.singletonList(pcalVarDecl("local", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
          labeled(label("l1"),
            assign(idexp("aWrite"), binop("-", idexp("x"), num(1))),
            assign(idexp("aRead"), idexp("aWrite")),
            ifS(
              binop(">=", idexp("aRead"), num(42)),
              util.Arrays.asList(
                assign(idexp("aWrite0"), binop("+", idexp("aWrite"), num(1))),
                assign(idexp("aWrite1"), binop("+", idexp("aWrite0"), num(42))),
                assign(idexp("aWrite2"), idexp("aWrite1")),
                assign(idexp("x"), idexp("aWrite2"))),
              util.Arrays.asList(
                assign(idexp("aWrite2"), idexp("x")),
                assign(idexp("x"), idexp("aWrite2"))))),
          labeled(label("l2"),
            assign(idexp("aWrite"), binop("+", idexp("x"), num(1))),
            assign(idexp("aWrite0"), binop("+", idexp("aWrite"), num(10))),
            assign(idexp("aWrite1"), binop("-", idexp("aWrite0"), num(1))),
            assign(idexp("aRead"), idexp("aWrite1")),
            assign(idexp("aWrite2"), binop("-", idexp("aWrite1"), num(1))),
            assign(idexp("aRead0"), idexp("aWrite2")),
            assign(idexp("bRead"), idexp("y")),
            assign(idexp("local"), binop("+", binop("+", idexp("aRead"), idexp("aRead0")), idexp("bRead"))),
            assign(idexp("x"), idexp("aWrite2"))), labeled(label("l3"),
            assign(idexp("aWrite"), binop("-", idexp("x"), num(1))),
            assign(idexp("aRead"), idexp("aWrite")), assign(idexp("bRead"), idexp("y")), assign(idexp("local"), binop("+", idexp("aRead"), idexp("bRead"))),
            assign(idexp("x"), idexp("aWrite"))),
          labeled(label("l4"),
            printS(idexp("local")))))
  }

  check("algorithm5") {
    """
      |----MODULE Algorithm5 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm5 {
      |  mapping macro TCPConnection {
      |    read {
      |      with (msg = Head($variable)) {
      |        $variable := Tail($variable);
      |        yield msg;
      |      }
      |    }
      |
      |    write {
      |      yield Append($variable, $value);
      |    }
      |  }
      |
      |  archetype AddClient(ref netw) {
      |      l1: netw := 21;
      |      l2: netw := 21;
      |          print netw;
      |  }
      |
      |  archetype AddServer(ref netw)
      |  variables a, b;
      |  {
      |      l1: a := netw;
      |          b := netw;
      |          netw := a + b;
      |  }
      |
      |  variable network = <<>>;
      |  fair process (S = 42) == instance AddServer(ref network)
      |  mapping network via TCPConnection;
      |  fair process (C = 21) == instance AddClient(ref network)
      |  mapping network via TCPConnection;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm5 {
      //     variables network = <<>>, netwRead, netwWrite, netwRead0, netwWrite0, netwWrite1,
      //               netwWrite2, netwRead1, netwWrite3;
      //     fair process (S = 42)
      //     variables a, b;
      //     {
      //         l1:
      //             with (msg0 = Head(network)) {
      //                 netwWrite := Tail(network);
      //                 netwRead := msg0;
      //             }
      //             a := netwRead;
      //             with (msg1 = Head(netwWrite)) {
      //                 netwWrite0 := Tail(netwWrite);
      //                 netwRead0 := msg1;
      //             }
      //             b := netwRead0;
      //             netwWrite1 := Append(netwWrite0,(a)+(b));
      //             network := netwWrite1;
      //
      //     }
      //     fair process (C = 42) {
      //         l1:
      //             netwWrite2 := Append(network,21);
      //             network := netwWrite2;
      //         l2:
      //             netwWrite2 := Append(network,21);
      //             with (msg2 = Head(netwWrite2)) {
      //                 netwWrite3 := Tail(netwWrite2);
      //                 netwRead1 := msg2;
      //             }
      //             print netwRead1;
      //             network := netwWrite3;
      //
      //     }
      // }
      algorithm(
        "Algorithm5",
        util.Arrays.asList(
          pcalVarDecl("network", false, false, tuple()),
          pcalVarDecl("netwRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite2", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwRead1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite3", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList,
        Collections.emptyList,
        Collections.emptyList,
        process(
          pcalVarDecl("S", false, false, num(42)),
          PlusCalFairness.WEAK_FAIR,
          util.Arrays.asList(
            pcalVarDecl("a", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
            pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
          labeled(label("l1"),
            `with`(
              Collections.singletonList(pcalVarDecl("msg0", false, false, opcall("Head", idexp("network")))),
              assign(idexp("netwWrite"), opcall("Tail", idexp("network"))),
              assign(idexp("netwRead"), idexp("msg0"))),
            assign(idexp("a"), idexp("netwRead")),
            `with`(
              Collections.singletonList(pcalVarDecl("msg1", false, false, opcall("Head", idexp("netwWrite")))),
              assign(idexp("netwWrite0"), opcall("Tail", idexp("netwWrite"))),
              assign(idexp("netwRead0"), idexp("msg1"))),
            assign(idexp("b"), idexp("netwRead0")),
            assign(idexp("netwWrite1"), opcall("Append", idexp("netwWrite0"), binop("+", idexp("a"), idexp("b")))),
            assign(idexp("network"), idexp("netwWrite1")))),
        process(
          pcalVarDecl("C", false, false, num(21)),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList,
          labeled(label("l1"),
            assign(idexp("netwWrite2"), opcall("Append", idexp("network"), num(21))),
            assign(idexp("network"), idexp("netwWrite2"))),
          labeled(label("l2"),
            assign(idexp("netwWrite2"), opcall("Append", idexp("network"), num(21))),
            `with`(
              Collections.singletonList(pcalVarDecl("msg2", false, false, opcall("Head", idexp("netwWrite2")))),
              assign(idexp("netwWrite3"), opcall("Tail", idexp("netwWrite2"))),
              assign(idexp("netwRead1"), idexp("msg2"))), printS(idexp("netwRead1")),
            assign(idexp("network"), idexp("netwWrite3")))))
  }

  check("algorithm6") {
    """
      |----MODULE Algorithm6 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm6 {
      |  mapping macro FunctionMapping {
      |    read {
      |      yield $variable;
      |    }
      |
      |    write {
      |      yield $value;
      |    }
      |  }
      |
      |  archetype A(ref f)
      |  {
      |      l1: f[0] := 1;
      |          f[1] := 0;
      |          print <<f[0], f[1]>>;
      |  }
      |
      |  variable func = [i \in {0, 1} |-> i];
      |  fair process (P = 42) == instance A(ref func)
      |  mapping func[_] via FunctionMapping;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm6 {
      //     variables func = [i \in {0,1} |-> i], fWrite, fWrite0, fRead, fRead0;
      //     fair process (P = 42) {
      //         l1:
      //             fWrite := [func EXCEPT ![0] = 1];
      //             fWrite0 := [fWrite EXCEPT ![1] = 0];
      //             fRead := fWrite0[0];
      //             fRead0 := fWrite0[1];
      //             print <<fRead,fRead0>>;
      //             func := fWrite0;
      //     }
      // }
      algorithm(
        "Algorithm6",
        util.Arrays.asList(
          pcalVarDecl("func", false, false,
            function(bounds(qbIds(Collections.singletonList(id("i")), set(num(0), num(1)))), idexp("i"))),
          pcalVarDecl("fWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("fWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("fRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("fRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList,
        Collections.emptyList,
        Collections.emptyList,
        process(
          pcalVarDecl("P", false, false, num(42)),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList,
          labeled(label("l1"),
            assign(idexp("fWrite"), fnSubst(idexp("func"), fnSubstPair(Collections.singletonList(substKey(num(0))), num(1)))),
            assign(idexp("fWrite0"), fnSubst(idexp("fWrite"), fnSubstPair(Collections.singletonList(substKey(num(1))), num(0)))),
            assign(idexp("fRead"), fncall(idexp("fWrite0"), num(0))),
            assign(idexp("fRead0"), fncall(idexp("fWrite0"), num(1))),
            printS(tuple(idexp("fRead"), idexp("fRead0"))),
            assign(idexp("func"), idexp("fWrite0")))))
  }

  check("algorithm7") {
    """
      |----MODULE Algorithm7 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm7 {
      |  mapping macro TCPConnection {
      |    read {
      |      with (msg = Head($variable)) {
      |        $variable := Tail($variable);
      |        yield msg;
      |      }
      |    }
      |
      |    write {
      |      yield Append($variable, $value);
      |    }
      |  }
      |
      |  archetype AddClient(ref netw) {
      |      l1: netw[self] := 21;
      |      l2: netw[self] := 21;
      |          print netw[self];
      |  }
      |
      |  archetype AddServer(ref netw)
      |  variables a, b, dest;
      |  {
      |      l1: either {
      |            a := netw[0];
      |            dest := 0;
      |          } or {
      |            a := netw[1];
      |            dest := 1;
      |          };
      |          b := netw[dest];
      |          netw[dest] := a + b;
      |  }
      |
      |  variable network = [i \in {0, 1} |-> <<>>];
      |  fair process (S = 42) == instance AddServer(ref network)
      |    mapping network[_] via TCPConnection;
      |  fair process (C \in {0, 1}) == instance AddClient(ref network)
      |    mapping network[_] via TCPConnection;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm7 {
      //     variables network = [i \in {0,1}|-><<>>], netwRead, netwWrite, netwRead0, netwWrite0,
      //               netwRead1, netwWrite1, netwWrite2, netwWrite3, netwRead2, netwWrite4;
      //     fair process (S = 42)
      //     variables a, b, dest;
      //     {
      //         l1:
      //             either {
      //                 with (msg0 = Head(network[0])) {
      //                     netwWrite := [network EXCEPT ![0] = Tail(network[0])];
      //                     netwRead := msg0;
      //                 }
      //                 a := netwRead;
      //                 dest := 0;
      //                 netwWrite0 := netwWrite;
      //             } or {
      //                 with (msg1 = Head(network[1])) {
      //                     netwWrite := [network EXCEPT ![1] = Tail(network[1])];
      //                     netwRead := msg1;
      //                 }
      //                 a := netwRead;
      //                 dest := 1;
      //                 netwWrite0 := netwWrite;
      //             }
      //             with (msg2 = Head(netwWrite0[dest])) {
      //                 netwWrite1 := [netwWrite0 EXCEPT ![dest] = Tail(netwWrite0[dest])];
      //                 netwRead0 := msg2;
      //             }
      //             b := netwRead0;
      //             netwWrite2 := [netwWrite1 EXCEPT ![dest] = Append(netwWrite1[dest], (a)+(b))];
      //             network = netwWrite2;
      //     }
      //     fair process (C \in {0,1}) {
      //         l1:
      //             netwWrite3 := [network EXCEPT ![self] = Append(network[self], 21)];
      //             network := netwWrite3;
      //         l2:
      //             netwWrite3 := [network EXCEPT ![self] = Append(network[self], 21)];
      //             with (msg3 = Head(netwWrite3[self])) {
      //                 netwWrite4 := [netwWrite3 EXCEPT ![self] = Tail(netwWrite3[self])];
      //                 netwRead1 := msg3;
      //             }
      //             print netwRead1;
      //             network := netWrite4;
      //     }
      // }
      algorithm(
        "Algorithm7",
        Arrays.asList(
          pcalVarDecl(
            "network",
            false,
            false,
            function(bounds(qbIds(Collections.singletonList(id("i")), set(num(0), num(1)))), tuple())),
          pcalVarDecl("netwRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwRead1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite2", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite3", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwRead2", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("netwWrite4", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("S", false, false, num(42)),
          PlusCalFairness.WEAK_FAIR,
          Arrays.asList(
            pcalVarDecl("a", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
            pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
            pcalVarDecl("dest", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
          labeled(
            label("l1"),
            either(Arrays.asList(
              Arrays.asList(
                `with`(
                  Collections.singletonList(pcalVarDecl("msg0", false, false, opcall("Head", fncall(idexp("network"), num(0))))),
                  assign(idexp("netwWrite"), fnSubst(idexp("network"), fnSubstPair(Collections.singletonList(substKey(num(0))), opcall("Tail", fncall(idexp("network"), num(0)))))),
                  assign(idexp("netwRead"), idexp("msg0"))),
                assign(idexp("a"), idexp("netwRead")),
                assign(idexp("dest"), num(0)),
                assign(idexp("netwWrite0"), idexp("netwWrite"))),
              Arrays.asList(
                `with`(
                  Collections.singletonList(pcalVarDecl("msg1", false, false, opcall("Head", fncall(idexp("network"), num(1))))),
                  assign(idexp("netwWrite"), fnSubst(idexp("network"), fnSubstPair(Collections.singletonList(substKey(num(1))), opcall("Tail", fncall(idexp("network"), num(1)))))),
                  assign(idexp("netwRead0"), idexp("msg1"))),
                assign(idexp("a"), idexp("netwRead0")),
                assign(idexp("dest"), num(1)),
                assign(idexp("netwWrite0"), idexp("netwWrite"))))),
            `with`(
              Collections.singletonList(pcalVarDecl("msg2", false, false, opcall("Head", fncall(idexp("netwWrite0"), idexp("dest"))))),
              assign(idexp("netwWrite1"), fnSubst(idexp("netwWrite0"), fnSubstPair(Collections.singletonList(substKey(idexp("dest"))), opcall("Tail", fncall(idexp("netwWrite0"), idexp("dest")))))),
              assign(idexp("netwRead1"), idexp("msg2"))),
            assign(idexp("b"), idexp("netwRead1")),
            assign(idexp("netwWrite2"), fnSubst(idexp("netwWrite1"), fnSubstPair(Collections.singletonList(substKey(idexp("dest"))), opcall("Append", fncall(idexp("netwWrite1"), idexp("dest")), binop("+", idexp("a"), idexp("b")))))),
            assign(idexp("network"), idexp("netwWrite2")))),
        process(
          pcalVarDecl("C", false, true, set(num(0), num(1))),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList(),
          labeled(
            label("l1"),
            assign(idexp("netwWrite3"), fnSubst(idexp("network"), fnSubstPair(Collections.singletonList(substKey(idexp("self"))), opcall("Append", fncall(idexp("network"), idexp("self")), num(21))))),
            assign(idexp("network"), idexp("netwWrite3"))),
          labeled(
            label("l2"),
            assign(idexp("netwWrite3"), fnSubst(idexp("network"), fnSubstPair(Collections.singletonList(substKey(idexp("self"))), opcall("Append", fncall(idexp("network"), idexp("self")), num(21))))),
            `with`(
              Collections.singletonList(pcalVarDecl("msg3", false, false, opcall("Head", fncall(idexp("netwWrite3"), idexp("self"))))),
              assign(idexp("netwWrite4"), fnSubst(idexp("netwWrite3"), fnSubstPair(Collections.singletonList(substKey(idexp("self"))), opcall("Tail", fncall(idexp("netwWrite3"), idexp("self")))))),
              assign(idexp("netwRead2"), idexp("msg3"))),
            printS(idexp("netwRead2")),
            assign(idexp("network"), idexp("netwWrite4")))))
  }

  check("algorithm8") {
    """
      |----MODULE Algorithm8 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm8 {
      |  mapping macro Identity {
      |      read  { yield $variable; }
      |      write { yield $value; }
      |  }
      |
      |  archetype Arch(ref mailboxes, ref other) {
      |      l: other := mailboxes[self];
      |  }
      |
      |  variables network = <<>>,
      |            processor = 0;
      |
      |  fair process (SomeProcess = 3) == instance Arch(ref network, ref processor)
      |      mapping network[_] via Identity;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm8 {
      //    variables network = <<>>, processor = 0, mailboxesRead, otherWrite;
      //    fair process (SomeProcess = 3) {
      //        l: mailboxesRead := network[self];
      //           otherWrite := mailboxesRead[self];
      //           processor := otherWrite;
      //    }
      algorithm(
        "Algorithm8",
        Arrays.asList(
          pcalVarDecl("network", false, false, tuple()),
          pcalVarDecl("processor", false, false, num(0)),
          pcalVarDecl("mailboxesRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("otherWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("SomeProcess", false, false, num(3)),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList(),
          labeled(
            label("l"),
            assign(idexp("mailboxesRead"), fncall(idexp("network"), idexp("self"))),
            assign(idexp("otherWrite"), idexp("mailboxesRead")),
            assign(idexp("processor"), idexp("otherWrite")))))
  }

  check("algorithm9") {
    """
      |----MODULE Algorithm9 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm9 {
      |  archetype A(ref a, b) {
      |      l1: if (b) {
      |            l2: a := 1;
      |            l3: a := 2;
      |          } else {
      |            a := 3;
      |          }
      |  }
      |
      |  variables i = 0, flag = TRUE;
      |
      |  process (P = 3) == instance A(ref i, flag);
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm9 {
      //     variables i = 0, flag = TRUE, bRead, aWrite, aWrite0;
      //     process (P = 3) {
      //         l1:
      //             bRead := flag;
      //             if (bRead) {
      //                 l2:
      //                     aWrite := 1;
      //                     i := aWrite;
      //
      //                 l3:
      //                     aWrite := 2;
      //                     i := aWrite;
      //
      //             } else {
      //                 aWrite := 3;
      //                 aWrite0 := aWrite;
      //                 i := aWrite0;
      //             }
      //
      //     }
      // }
      algorithm(
        "Algorithm9",
        Arrays.asList(
          pcalVarDecl("i", false, false, num(0)),
          pcalVarDecl("flag", false, false, bool(true)),
          pcalVarDecl("bRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("P", false, false, num(3)),
          PlusCalFairness.UNFAIR,
          Collections.emptyList(),
          labeled(
            label("l1"),
            assign(idexp("bRead"), idexp("flag")),
            ifS(
              idexp("bRead"),
              Arrays.asList(
                labeled(
                  label("l2"),
                  assign(idexp("aWrite"), num(1)),
                  assign(idexp("i"), idexp("aWrite"))),
                labeled(
                  label("l3"),
                  assign(idexp("aWrite"), num(2)),
                  assign(idexp("i"), idexp("aWrite")))),
              Arrays.asList(
                assign(idexp("aWrite"), num(3)),
                assign(idexp("aWrite0"), idexp("aWrite")),
                assign(idexp("i"), idexp("aWrite0")))))))
  }

  check("algorithm10") {
    """
      |----MODULE Algorithm10 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal WhileLoopWithFollowingStatement {
      |	 archetype Valid(ref aBool) {
      |      l:
      |        while (aBool) {
      |          either { skip }
      |          or {
      |              l1:
      |                while (aBool) {
      |                    skip;
      |                };
      |                aBool := FALSE;
      |          }
      |        };
      |        print "ok";
      |	 }
      |
      |  variable b = TRUE;
      |  fair process (P = 10) == instance Valid(b);
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm WhileLoopWithFollowingStatement {
      //    variables b = TRUE, aBoolRead, aBoolRead0, aBoolWrite, aBoolWrite0, aBoolWrite1, aBoolWrite2;
      //    process (P = 10) {
      //        l:
      //            aBoolRead := b;
      //            if (aBoolRead) {
      //                either {
      //                    aBoolWrite1 := b;
      //                    aBoolWrite2 := aBoolWrite1;
      //                    b := aBoolWrite2;
      //                    goto l;
      //                } or {
      //                    l1:
      //                        aBoolRead0 := b;
      //                        if (aBoolRead0) {
      //                            aBoolWrite0 := b;
      //                            b := aBoolWrite0;
      //                            goto l1;
      //                        } else {
      //                            aBoolWrite := FALSE;
      //                            aBoolWrite0 := aBoolWrite;
      //                            b := aBoolWrite0;
      //                            goto l;
      //                        }
      //
      //                }
      //            } else {
      //                print "ok";
      //                aBoolWrite2 := b;
      //                b := aBoolWrite2;
      //            }
      //
      //    }
      // }
      algorithm(
        "WhileLoopWithFollowingStatement",
        Arrays.asList(
          pcalVarDecl("b", false, false, bool(true)),
          pcalVarDecl("aBoolRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aBoolWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aBoolWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aBoolWrite1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aBoolWrite2", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("P", false, false, num(10)),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList(),
          labeled(
            label("l"),
            assign(idexp("aBoolRead"), idexp("b")),
            ifS(
              idexp("aBoolRead"),
              Collections.singletonList(
                either(Arrays.asList(
                  Arrays.asList(
                    assign(idexp("aBoolWrite1"), idexp("b")),
                    assign(idexp("aBoolWrite2"), idexp("aBoolWrite1")),
                    assign(idexp("b"), idexp("aBoolWrite2")),
                    gotoS("l")),
                  Collections.singletonList(
                    labeled(
                      label("l1"),
                      assign(idexp("aBoolRead"), idexp("b")),
                      ifS(
                        idexp("aBoolRead"),
                        Arrays.asList(
                          assign(idexp("aBoolWrite0"), idexp("b")),
                          assign(idexp("b"), idexp("aBoolWrite0")),
                          gotoS("l1")),
                        Arrays.asList(
                          assign(idexp("aBoolWrite"), bool(false)),
                          assign(idexp("aBoolWrite0"), idexp("aBoolWrite")),
                          assign(idexp("b"), idexp("aBoolWrite0")),
                          gotoS("l")))))))),
              Arrays.asList(
                printS(str("ok")),
                assign(idexp("aBoolWrite2"), idexp("b")),
                assign(idexp("b"), idexp("aBoolWrite2")))))))
  }

  check("algorithm11") {
    """
      |----MODULE Algorithm11 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm11 {
      |  procedure P(ref a1, a2) {
      |    l3:
      |      while (a1 < 10 /\ a2) {
      |        a1 := 1;
      |      }
      |  }
      |
      |  mapping macro Adder {
      |    read {
      |      yield $variable;
      |    }
      |    write {
      |      yield $variable + $value;
      |    }
      |  }
      |
      |  archetype A(ref a, b) {
      |    l1:
      |      a := 1;
      |      call P(ref a, b);
      |    l2:
      |      call P(ref a, b);
      |  }
      |
      |  variables i = 0, flag = TRUE;
      |
      |  fair process (Proc = 0) == instance A(ref i, flag)
      |  mapping i via Adder;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm11 {
      //     variables i = 0, flag = TRUE, aWrite;
      //     procedure P0 ()
      //     variables local, a1Read, a2Read, a1Write, a1Write0;
      //     {
      //         l3:
      //             a1Read := i;
      //             a2Read := flag;
      //             if (a1Read < 10 /\ a2Read) {
      //                 a1Write := i + 1;
      //                 a1Write0 := a1Write;
      //                 i := a1Write0;
      //                 goto l2;
      //             } else {
      //                 a1Write0 := i;
      //                 i := a1Write0;
      //             }
      //
      //     }
      //     fair process (Proc = 0) {
      //         l1:
      //             aWrite := i + 1;
      //             i := aWrite;
      //             call P0();
      //         l2:
      //             call P0();
      //
      //     }
      // }
      algorithm(
        "Algorithm11",
        Arrays.asList(
          pcalVarDecl("i", false, false, num(0)),
          pcalVarDecl("flag", false, false, bool(true)),
          pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList(),
        Collections.singletonList(
          procedure(
            "P0",
            Collections.emptyList(),
            Arrays.asList(
              pcalVarDecl("a1Read", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
              pcalVarDecl("a2Read", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
              pcalVarDecl("a1Write", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
              pcalVarDecl("a1Write0", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
            labeled(
              label("l3"),
              assign(idexp("a1Read"), idexp("i")),
              assign(idexp("a2Read"), idexp("flag")),
              ifS(
                binop("/\\", binop("<", idexp("a1Read"), num(10)), idexp("a2Read")),
                Arrays.asList(
                  assign(idexp("a1Write"), binop("+", idexp("i"), num(1))),
                  assign(idexp("a1Write0"), idexp("a1Write")),
                  assign(idexp("i"), idexp("a1Write0")),
                  gotoS("l3")),
                Arrays.asList(
                  assign(idexp("a1Write0"), idexp("i")),
                  assign(idexp("i"), idexp("a1Write0"))))))),
        Collections.emptyList(),
        process(
          pcalVarDecl("Proc", false, false, num(0)),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList(),
          labeled(
            label("l1"),
            assign(idexp("aWrite"), binop("+", idexp("i"), num(1))),
            assign(idexp("i"), idexp("aWrite")),
            call("P0")),
          labeled(
            label("l2"),
            call("P0"))))
  }

  check("algorithm12") {
    """
      |----MODULE Algorithm12 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm12 {
      |  archetype A(a)
      |  variable local = 0;
      |  {
      |    l1:
      |      local := a + 1;
      |      print <<a, local>>;
      |  }
      |
      |  variables i = 0;
      |
      |  fair process (Proc = 0) == instance A(i * 2 + 1);
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm12 {
      //     variables i = 0, aRead, aRead0;
      //     fair process (Proc = 0)
      //     variables aLocal = i * 2 + 1, local = 0;
      //     {
      //         l1:
      //             aRead := aLocal;
      //             local := aRead + 1;
      //             aRead0 := aLocal;
      //             print <<aRead0, local>>;
      //     }
      // }
      algorithm(
        "Algorithm12",
        Arrays.asList(
          pcalVarDecl("i", false, false, num(0)),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("Proc", false, false, num(0)),
          PlusCalFairness.WEAK_FAIR,
          Arrays.asList(
            pcalVarDecl("aLocal", false, false, binop("+", binop("*", idexp("i"), num(2)), num(1))),
            pcalVarDecl("local", false, false, num(0))),
          labeled(
            label("l1"),
            assign(idexp("aRead"), idexp("aLocal")),
            assign(idexp("local"), binop("+", idexp("aRead"), num(1))),
            assign(idexp("aRead0"), idexp("aLocal")),
            printS(tuple(idexp("aRead0"), idexp("local"))))))
  }

  check("algorithm13") {
    """
      |----MODULE Algorithm13 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm13 {
      |  archetype A(ref a) {
      |    l1:
      |      a := a + 1;
      |      print a;
      |  }
      |
      |  variables i = 0;
      |
      |  fair process (Proc = 0) == instance A(ref i);
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm13 {
      //     variables i = 0, aRead, aWrite, aRead0;
      //     fair process (Proc = 0) {
      //         l1:
      //             aRead := i;
      //             aWrite := aRead + 1;
      //             aRead0 := aWrite;
      //             print aRead0;
      //             i := aWrite;
      //     }
      // }
      algorithm(
        "Algorithm13",
        Arrays.asList(
          pcalVarDecl("i", false, false, num(0)),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("Proc", false, false, num(0)),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList(),
          labeled(
            label("l1"),
            assign(idexp("aRead"), idexp("i")),
            assign(idexp("aWrite"), binop("+", idexp("aRead"), num(1))),
            assign(idexp("aRead0"), idexp("aWrite")),
            printS(idexp("aRead0")),
            assign(idexp("i"), idexp("aWrite")))))
  }

  check("algorithm14") {
    """
      |----MODULE Algorithm14 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm14 {
      |  archetype A(a, b)
      |  variable local = 0;
      |  {
      |    l1:
      |      local := a + 1;
      |      if (b) {
      |          print <<a, local>>;
      |      } else {
      |          print <<local, a + 1>>;
      |          l2:
      |              print a + 2;
      |      };
      |  }
      |
      |  variables i = 0, flag = TRUE;
      |
      |  fair process (Proc = 0) == instance A(i * 2 + 1, flag);
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm14 {
      //     variables i = 0, flag = TRUE, aRead, bRead, aRead0, aRead1;
      //     fair process (Proc = 0)
      //     variables aLocal = i * 2 + 1, local = 0;
      //     {
      //         l1:
      //             aRead := aLocal;
      //             local := aRead + 1;
      //             bRead := flag;
      //             if (bRead) {
      //                 aRead0 := aLocal;
      //                 print <<aRead0, local>>;
      //             } else {
      //                 aRead1 := aLocal;
      //                 print <<local, aRead1 + 1>>;
      //                 l2:
      //                     aRead := aLocal;
      //                     print aRead + 2;
      //             };
      //     }
      // }
      algorithm(
        "Algorithm14",
        Arrays.asList(
          pcalVarDecl("i", false, false, num(0)),
          pcalVarDecl("flag", false, false, bool(true)),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("bRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aRead1", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
        ),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("Proc", false, false, num(0)),
          PlusCalFairness.WEAK_FAIR,
          Arrays.asList(
            pcalVarDecl("aLocal", false, false, binop("+", binop("*", idexp("i"), num(2)), num(1))),
            pcalVarDecl("local", false, false, num(0))),
          labeled(
            label("l1"),
            assign(idexp("aRead"), idexp("aLocal")),
            assign(idexp("local"), binop("+", idexp("aRead"), num(1))),
            assign(idexp("bRead"), idexp("flag")),
            ifS(
              idexp("bRead"),
              Arrays.asList(
                assign(idexp("aRead0"), idexp("aLocal")),
                printS(tuple(idexp("aRead0"), idexp("local")))),
              Arrays.asList(
                assign(idexp("aRead1"), idexp("aLocal")),
                printS(tuple(idexp("local"), binop("+", idexp("aRead1"), num(1)))),
                labeled(
                  label("l2"),
                  assign(idexp("aRead"), idexp("aLocal")),
                  printS(binop("+", idexp("aRead"), num(2)))))))))
  }

  check("algorithm15") {
    """
      |----MODULE Algorithm15 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm15 {
      |  archetype A(ref a)
      |  variables local1 = 0, local2 = local1 + 1;
      |  {
      |    l1:
      |      a := a + 1;
      |      print <<a, local1, local2>>;
      |  }
      |
      |  variables i = 0;
      |
      |  fair process (Proc = 0) == instance A(ref i);
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm15 {
      //     variables i = 0, aRead, aWrite, aRead0;
      //     fair process (Proc = 0)
      //     variables local1 = 0, local2 = local1 + 1;
      //     {
      //         l1:
      //             aRead := i;
      //             aWrite := aRead + 1;
      //             aRead0 := aWrite;
      //             print <<aRead0, local1, local2>>;
      //             i := aWrite;
      //     }
      // }
      algorithm(
        "Algorithm15",
        Arrays.asList(
          pcalVarDecl("i", false, false, num(0)),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("Proc", false, false, num(0)),
          PlusCalFairness.WEAK_FAIR,
          Arrays.asList(
            pcalVarDecl("local1", false, false, num(0)),
            pcalVarDecl("local2", false, false, binop("+", idexp("local1"), num(1)))),
          labeled(
            label("l1"),
            assign(idexp("aRead"), idexp("i")),
            assign(idexp("aWrite"), binop("+", idexp("aRead"), num(1))),
            assign(idexp("aRead0"), idexp("aWrite")),
            printS(tuple(idexp("aRead0"), idexp("local1"), idexp("local2"))),
            assign(idexp("i"), idexp("aWrite")))))
  }

  check("algorithm16") {
    """
      |----MODULE Algorithm16 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm16 {
      |  archetype A(ref a)
      |  variables local1 = a, local2 = local1 + 1;
      |  {
      |    l1:
      |      a := a + 1;
      |      print <<a, local1, local2>>;
      |  }
      |
      |  variables i = 0;
      |
      |  fair process (Proc = 0) == instance A(ref i);
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm16 {
      //     variables i = 0, aRead, aWrite, aRead0;
      //     fair process (Proc = 0)
      //     variables local1, local2;
      //     {
      //         init:
      //             aRead := i;
      //             local1 := aRead;
      //             local2 := local1 + 1;
      //         l1:
      //             aRead := i;
      //             aWrite := aRead + 1;
      //             aRead0 := aWrite;
      //             print <<aRead0, local1, local2>>;
      //             i := aWrite;
      //     }
      // }
      algorithm(
        "Algorithm16",
        Arrays.asList(
          pcalVarDecl("i", false, false, num(0)),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("Proc", false, false, num(0)),
          PlusCalFairness.WEAK_FAIR,
          Arrays.asList(
            pcalVarDecl("local1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
            pcalVarDecl("local2", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
          ),
          labeled(
            label("init"),
            assign(idexp("aRead"), idexp("i")),
            assign(idexp("local1"), idexp("aRead")),
            assign(idexp("local2"), binop("+", idexp("local1"), num(1)))
          ),
          labeled(
            label("l1"),
            assign(idexp("aRead"), idexp("i")),
            assign(idexp("aWrite"), binop("+", idexp("aRead"), num(1))),
            assign(idexp("aRead0"), idexp("aWrite")),
            printS(tuple(idexp("aRead0"), idexp("local1"), idexp("local2"))),
            assign(idexp("i"), idexp("aWrite"))
          )))
  }

  check("algorithm17") {
    """
      |----MODULE Algorithm17 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm17 {
      |  archetype A()
      |  {
      |    l1:
      |        if (TRUE) {
      |            skip;
      |        };
      |  }
      |
      |  fair process (Proc = 0) == instance A();
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm17 {
      //     fair process (Proc = 0) {
      //         l1:
      //             if (TRUE) {
      //                 skip;
      //             };
      //     }
      // }
      algorithm(
        "Algorithm17",
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("Proc", false, false, num(0)),
          PlusCalFairness.WEAK_FAIR,
          Collections.emptyList(),
          labeled(
            label("l1"),
            ifS(
              bool(true),
              Collections.singletonList(skip()),
              Collections.emptyList()))))
  }

  check("algorithm18") {
    """
      |----MODULE Algorithm18 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm18 {
      |  mapping macro Macro {
      |    read {
      |      yield $variable;
      |    }
      |    write {
      |      yield $variable + $value;
      |    }
      |  }
      |  archetype A(ref a)
      |  {
      |    l1:
      |      a := 1;
      |      print a;
      |  }
      |
      |  fair process (Proc = 0) == instance A(0)
      |    mapping @1 via Macro;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm18 {
      //     variables aWrite, aRead;
      //     fair process (Proc = 0)
      //     variables aLocal = 0;
      //     {
      //         l1:
      //           aWrite := aLocal + 1;
      //           aRead := aWrite;
      //           print aRead;
      //           aLocal := aWrite;
      //     }
      // }
      algorithm(
        "Algorithm18",
        Arrays.asList(
          pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
        ),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("Proc", false, false, num(0)),
          PlusCalFairness.WEAK_FAIR,
          Collections.singletonList(
            pcalVarDecl("aLocal", false, false, num(0))
          ),
          labeled(
            label("l1"),
            assign(idexp("aWrite"), binop("+", idexp("aLocal"), num(1))),
            assign(idexp("aRead"), idexp("aWrite")),
            printS(idexp("aRead")),
            assign(idexp("aLocal"), idexp("aWrite")))))
  }

  check("algorithm19") {
    """
      |----MODULE Algorithm19 ----
      |EXTENDS TLC, Sequences, FiniteSets, Integers
      |(*
      |--mpcal Algorithm19 {
      |  mapping macro Macro {
      |    read {
      |      yield $variable;
      |    }
      |    write {
      |      yield $variable + $value;
      |    }
      |  }
      |  archetype A(ref a)
      |  {
      |    l1:
      |      a[1] := 1;
      |      print a[1];
      |  }
      |
      |  fair process (Proc = 0) == instance A(<<0>>)
      |    mapping @1[_] via Macro;
      |}
      |*)
      |\* BEGIN TRANSLATION
      |====
      |""".stripMargin ->
      // --algorithm Algorithm19 {
      //     variables aWrite, aRead;
      //     fair process (Proc = 0)
      //     variables aLocal = <<0>>;
      //     {
      //         l1:
      //           aWrite := [aLocal EXCEPT ![1] = aLocal[1] + 1];
      //           aRead := aWrite[1];
      //           print aRead;
      //           aLocal := aWrite;
      //     }
      // }
      algorithm(
        "Algorithm19",
        Arrays.asList(
          pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
          pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
        ),
        Collections.emptyList(),
        Collections.emptyList(),
        Collections.emptyList(),
        process(
          pcalVarDecl("Proc", false, false, num(0)),
          PlusCalFairness.WEAK_FAIR,
          Collections.singletonList(
            pcalVarDecl("aLocal", false, false, tuple(num(0)))
          ),
          labeled(
            label("l1"),
            assign(
              idexp("aWrite"),
              fnSubst(
                idexp("aLocal"),
                fnSubstPair(
                  Collections.singletonList(key(num(1))),
                  binop("+", fncall(idexp("aLocal"), num(1)), num(1))))),
            assign(idexp("aRead"), fncall(idexp("aWrite"), num(1))),
            printS(idexp("aRead")),
            assign(idexp("aLocal"), idexp("aWrite")))))
  }

}
