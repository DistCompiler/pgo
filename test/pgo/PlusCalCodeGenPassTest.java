package pgo;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import pgo.errors.TopLevelIssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.pcal.PlusCalFairness;
import pgo.model.tla.TLAIdentifier;
import pgo.model.tla.TLAModule;
import pgo.trans.PGoTransException;
import pgo.util.SourceLocation;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;
import static pgo.model.mpcal.ModularPlusCalBuilder.*;
import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class PlusCalCodeGenPassTest {

	@Parameters
	public static List<Object[]> testCases(){
		return Arrays.asList(new Object[][] {
				// -- mpcal Algorithm1 {
				//     archetype A1(a) {
				//         l1: skip;
				//     }
				//
				//     variable x = 10;
				//     process (P1 = 42) == instance A1(x);
				// }
				{
						mpcal(
								"Algorithm1",
								Collections.singletonList(
										pcalVarDecl("x", false, false, num(10))
								),
								Collections.emptyList(),
								Collections.singletonList(
										archetype(
												"A1",
												Collections.singletonList(
														pcalVarDecl("a", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
												),
												Collections.emptyList(),
												Collections.singletonList(
														labeled(label("l1"), skip())
												)
										)
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										instance(
												pcalVarDecl("P1", false, false, num(42)),
												PlusCalFairness.WEAK_FAIR,
												"A1",
												Collections.singletonList(
														idexp("x")
												),
												Collections.emptyList()
										)
								)
						),

						// -- algorithm Algorithm1 {
						//     variable x = 10;

						//     process (P1 = 42) {
						//         l1: skip;
						//     }
						// }
						algorithm(
								"Algorithm1",
								Collections.singletonList(
										pcalVarDecl("x", false, false, num(10))
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								process(
										pcalVarDecl("P1", false, false, num(42)),
										PlusCalFairness.WEAK_FAIR,
										Collections.emptyList(),
										labeled(label("l1"), skip())
								)
						)
				},

				// --mpcal Algorithm2 {
				//     mapping macro Zero {
				//         read {
				//             yield 0
				//         }
				//         write {
				//             yield $variable
				//         }
				//     }
				//     archetype A1(a, ref b) {
				//         l1: print << a, b >>;
				//     }
				//
				//     variables x = 10, y = 20;
				//     process (P1 = 42) == instance A1(x, ref y)
				//     mapping x via Zero;
				// }
				{
						mpcal(
								"Algorithm2",
								Arrays.asList(
										pcalVarDecl("x", false, false, num(10)),
										pcalVarDecl("y", false, false, num(20))
								),
								Collections.singletonList(
										mappingMacro(
												"Zero",
												Collections.singletonList(yield(num(0))),
												Collections.singletonList(yield(DOLLAR_VARIABLE))
										)
								),
								Collections.singletonList(
										archetype(
												"A1",
												Arrays.asList(
														pcalVarDecl("a", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
														pcalVarDecl("b", true, false, PLUSCAL_DEFAULT_INIT_VALUE)
												),
												Collections.emptyList(),
												Collections.singletonList(labeled(
														label("l1"),
														printS(tuple(idexp("a"), idexp("b")))
												))
										)
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										instance(
												pcalVarDecl("P1", false, false, num(42)),
												PlusCalFairness.WEAK_FAIR,
												"A1",
												Arrays.asList(
														idexp("x"),
														ref("y")
												),
												Collections.singletonList(
														mapping("x", "Zero", false)
												)
										)
								)
						),

						// --algorithm Algorithm2 {
						//     variables x = 10, y = 20;
						//     process (P1 = 42)
						//     variables aRead, bRead; {
						//         l1: aRead := 0;
						//             bRead := y;
						//             print << (aRead), (bRead) >>;
						//     }
						// }
						algorithm(
								"Algorithm2",
								Arrays.asList(
										pcalVarDecl("x", false, false, num(10)),
										pcalVarDecl("y", false, false, num(20))
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								process(
										pcalVarDecl("P1", false, false, num(42)),
										PlusCalFairness.WEAK_FAIR,
										Arrays.asList(
												pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("bRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
										),
										labeled(
												label("l1"),
												assign(idexp("aRead"), num(0)),
												assign(idexp("bRead"), idexp("y")),
												printS(tuple(idexp("aRead"), idexp("bRead")))
										)
								)
						)
				},

				{
						// --mpcal Algorithm3 {
						//    mapping macro WeirdMacro {
						//        read {
						//            $variable := $variable - 1;
						//            with (v = 50) {
						//                either { yield v } or { yield 10 }
						//            }
						//        }
						//        write {
						//            yield $value + 1
						//        }
						//    }
						//    archetype A1(ref a, b)
						//    variable local; {
						//        l1: if (a >= 42) {
						//                local := 42;
						//            }
						//        l2: a := 10;
						//        l3: local := a + b;
						//        l4: print local;
						//    }
						//    variables x = 10, y = 20;
						//    process (P1 = 100) == instance A1(ref x, y)
						//    mapping x via WeirdMacro;
						// }

						mpcal(
								"Algorithm3",
								Arrays.asList(
										pcalVarDecl("x", false, false, num(10)),
										pcalVarDecl("y", false, false, num(20))
								),
								Collections.singletonList(
										mappingMacro(
												"WeirdMacro",
												Arrays.asList(
														assign(DOLLAR_VARIABLE, binop("-", DOLLAR_VARIABLE, num(1))),
														with(
																Collections.singletonList(pcalVarDecl("v", false, false, num(50))),
																either(
																		Arrays.asList(
																				Collections.singletonList(yield(idexp("v"))),
																				Collections.singletonList(yield(num(10)))
																		)
																)
														)
												),
												Collections.singletonList(yield(binop("+", DOLLAR_VALUE, num(1))))
										)
								),
								Collections.singletonList(
										archetype(
												"A1",
												Arrays.asList(
														pcalVarDecl("a", true, false, PLUSCAL_DEFAULT_INIT_VALUE),
														pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
												),
												Collections.singletonList(pcalVarDecl("local", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Arrays.asList(
														labeled(
																label("l1"),
																ifS(
																		binop(">=", idexp("a"), num(42)),
																		Collections.singletonList(assign(idexp("local"), num(42))),
																		Collections.emptyList()
																)
														),

														labeled(
																label("l2"),
																assign(idexp("a"), num(10))
														),

														labeled(
																label("l3"),
																assign(idexp("local"), binop("+", idexp("a"), idexp("b")))
														),

														labeled(
																label("l4"),
																printS(idexp("local"))
														)
												)
										)
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										instance(
												pcalVarDecl("P1", false, false, num(100)),
												PlusCalFairness.WEAK_FAIR,
												"A1",
												Arrays.asList(
														ref("x"),
														idexp("y")
												),
												Collections.singletonList(
														mapping(
																"x",
																"WeirdMacro",
																false
														)
												)
										)
								)
						),

						// --algorithm Algorithm3 {
						//    variables x = 10, y = 20;
						//    process (P1 = 100)
						//    variables local, aRead, aWrite, bRead;
						//    {
						//        l1:
						//            aWrite := (x)-(1);
						//            with (v0 = 50) {
						//                either {
						//                    aRead := v0;
						//                } or {
						//                    aRead := 10;
						//                }
						//            }
						//            if ((aRead)>=(42)) {
						//                local := 42;
						//            }
						//            x := aWrite;
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
						//                }
						//            }
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
								Arrays.asList(
										pcalVarDecl("x", false, false, num(10)),
										pcalVarDecl("y", false, false, num(20))
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								process(
										pcalVarDecl("P1", false, false, num(100)),
										PlusCalFairness.WEAK_FAIR,
										Arrays.asList(
												pcalVarDecl("local", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("bRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
										),
										labeled(
												label("l1"),
												assign(idexp("aWrite"), binop("-", idexp("x"), num(1))),
												with(
														Collections.singletonList(pcalVarDecl("v0", false, false, num(50))),
														either(
																Arrays.asList(
																		Collections.singletonList(assign(idexp("aRead"), idexp("v0"))),
																		Collections.singletonList(assign(idexp("aRead"), num(10)))
																)
														)
												),
												ifS(
														binop(">=", idexp("aRead"), num(42)),
														Collections.singletonList(assign(idexp("local"), num(42))),
														Collections.emptyList()
												),
												assign(idexp("x"), idexp("aWrite"))
										),

										labeled(
												label("l2"),
												assign(idexp("aWrite"), binop("+", num(10), num(1))),
												assign(idexp("x"), idexp("aWrite"))
										),

										labeled(
												label("l3"),
												assign(idexp("aWrite"), binop("-", idexp("x"), num(1))),
												with(
														Collections.singletonList(pcalVarDecl("v1", false, false, num(50))),
														either(
																Arrays.asList(
																		Collections.singletonList(assign(idexp("aRead"), idexp("v1"))),
																		Collections.singletonList(assign(idexp("aRead"), num(10)))
																)
														)
												),
												assign(idexp("bRead"), idexp("y")),
												assign(idexp("local"), binop("+", idexp("aRead"), idexp("bRead"))),
												assign(idexp("x"), idexp("aWrite"))
										),

										labeled(
												label("l4"),
												printS(idexp("local"))
										)
								)
						)
				},

				{
						// --mpcal Algorithm4 {
						//     mapping macro WeirdMacro {
						//         read {
						//             $variable := $variable - 1;
						//             yield $variable;
						//         }
						//         write {
						//             $variable := $variable + 1;
						//             yield $variable + $value;
						//         }
						//     }
						//     archetype A1(ref a, b)
						//     variable local; {
						//         l1: if (a >= 42) {
						//                 a := 42;
						//             }
						//         l2: a := 10;
						//             local := a + a + b;
						//         l3: local := a + b;
						//         l4: print local;
						//     }
						//     variables x = 10, y = 20;
						//     process (P1 = 42) == instance A1(ref x, y)
						//     mapping x via WeirdMacro;
						// }
						mpcal(
								"Algorithm4",
								Arrays.asList(
										pcalVarDecl("x", false, false, num(10)),
										pcalVarDecl("y", false, false, num(20))
								),
								Collections.singletonList(
										mappingMacro(
												"WeirdMacro",
												Arrays.asList(
														assign(DOLLAR_VARIABLE, binop("-", DOLLAR_VARIABLE, num(1))),
														yield(DOLLAR_VARIABLE)
												),
												Arrays.asList(
														assign(DOLLAR_VARIABLE, binop("+", DOLLAR_VARIABLE, num(1))),
														yield(binop("+", DOLLAR_VARIABLE, DOLLAR_VALUE))
												)
										)
								),
								Collections.singletonList(
										archetype(
												"A1",
												Arrays.asList(
														pcalVarDecl("a", true, false, PLUSCAL_DEFAULT_INIT_VALUE),
														pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
												),
												Collections.singletonList(pcalVarDecl("local", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Arrays.asList(
														labeled(
																label("l1"),
																ifS(
																		binop(">=", idexp("a"), num(42)),
																		Collections.singletonList(assign(idexp("a"), num(42))),
																		Collections.emptyList()
																)
														),

														labeled(
																label("l2"),
																assign(idexp("a"), num(10)),
																assign(idexp("local"), binop("+", binop("+", idexp("a"), idexp("a")), idexp("b")))
														),

														labeled(
																label("l3"),
																assign(idexp("local"), binop("+", idexp("a"), idexp("b")))
														),

														labeled(
																label("l4"),
																printS(idexp("local"))
														)
												)
										)
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										instance(
												pcalVarDecl("P1", false, false, num(100)),
												PlusCalFairness.WEAK_FAIR,
												"A1",
												Arrays.asList(
														ref("x"),
														idexp("y")
												),
												Collections.singletonList(
														mapping(
																"x",
																"WeirdMacro",
																false
														)
												)
										)
								)
						),
						// --algorithm Algorithm4 {
						//     variables x = 10, y = 20;
						//     process (P1 = 42)
						//     variables local, aRead, aWrite, aWrite0, aWrite1, aRead0, bRead;
						//     {
						//         l1:
						//             aWrite := (x)-(1);
						//             aRead := aWrite;
						//             if ((aRead)>=(42)) {
						//                 aWrite0 := (aWrite)+(1);
						//                 aWrite1 := (aWrite0)+(42);
						//                 aWrite2 := aWrite1;
						//             } else {
						//                 aWrite2 := x;
						//             }
						//             x := aWrite2;
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
								Arrays.asList(
										pcalVarDecl("x", false, false, num(10)),
										pcalVarDecl("y", false, false, num(20))
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								process(
										pcalVarDecl("P1", false, false, num(100)),
										PlusCalFairness.WEAK_FAIR,
										Arrays.asList(
												pcalVarDecl("local", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("aWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("aWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("aWrite1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("aWrite2", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("aRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("bRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
										),
										labeled(
												label("l1"),
												assign(idexp("aWrite"), binop("-", idexp("x"), num(1))),
												assign(idexp("aRead"), idexp("aWrite")),
												ifS(
														binop(">=", idexp("aRead"), num(42)),
														Arrays.asList(
																assign(idexp("aWrite0"), binop("+", idexp("aWrite"), num(1))),
																assign(idexp("aWrite1"), binop("+", idexp("aWrite0"), num(42))),
																assign(idexp("aWrite2"), idexp("aWrite1"))
														),
														Collections.singletonList(
																assign(idexp("aWrite2"), idexp("x"))
														)
												),
												assign(idexp("x"), idexp("aWrite2"))
										),

										labeled(
												label("l2"),
												assign(idexp("aWrite"), binop("+", idexp("x"), num(1))),
												assign(idexp("aWrite0"), binop("+", idexp("aWrite"), num(10))),
												assign(idexp("aWrite1"), binop("-", idexp("aWrite0"), num(1))),
												assign(idexp("aRead"), idexp("aWrite1")),
												assign(idexp("aWrite2"), binop("-", idexp("aWrite1"), num(1))),
												assign(idexp("aRead0"), idexp("aWrite2")),
												assign(idexp("bRead"), idexp("y")),
												assign(idexp("local"), binop("+", binop("+", idexp("aRead"), idexp("aRead0")), idexp("bRead"))),
												assign(idexp("x"), idexp("aWrite2"))
										),

										labeled(
												label("l3"),
												assign(idexp("aWrite"), binop("-", idexp("x"), num(1))),
												assign(idexp("aRead"), idexp("aWrite")),
												assign(idexp("bRead"), idexp("y")),
												assign(idexp("local"), binop("+", idexp("aRead"), idexp("bRead"))),
												assign(idexp("x"), idexp("aWrite"))
										),

										labeled(
												label("l4"),
												printS(idexp("local"))
										)
								)
						)
				},

				{
						// --mpcal Algorithm5 {
						//   mapping macro TCPConnection {
						//     read {
						//       with (msg = Head($variable)) {
						//         $variable := Tail($variable);
						//         yield msg;
						//       }
						//     }
						//
						//     write {
						//       yield Append($variable, $value);
						//     }
						//   }
						//
						//   archetype AddClient(ref netw) {
						//       l1: netw := 21;
						//       l2: netw := 21;
						//           print netw;
						//   }
						//
						//   archetype AddServer(ref netw)
						//   variables a, b;
						//   {
						//       l1: a := netw;
						//           b := netw;
						//           netw := a + b;
						//   }
						//
						//   variable network = <<>>;
						//   process (S = 42) == instance AddServer(ref network)
						//   mapping network via TCPConnection;
						//   process (C = 21) == instance AddClient(ref network)
						//   mapping network via TCPConnection;
						// }
						mpcal(
								"Algorithm5",
								Collections.singletonList(pcalVarDecl("network", false, false, tuple()) ),
								Collections.singletonList(
										mappingMacro(
												"TCPConnection",
												Collections.singletonList(
														with(
																Collections.singletonList(pcalVarDecl("msg", false, false, opcall("Head", DOLLAR_VARIABLE))),
																assign(DOLLAR_VARIABLE, opcall("Tail", DOLLAR_VARIABLE)),
																yield(idexp("msg")))
												),
												Collections.singletonList(
														yield(opcall("Append", DOLLAR_VARIABLE, DOLLAR_VALUE))
												)
										)
								),
								Arrays.asList(
										archetype(
												"AddClient",
												Collections.singletonList(pcalVarDecl("netw", true, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Collections.emptyList(),
												Arrays.asList(
														labeled(
																label("l1"),
																assign(idexp("netw"), num(21))),
														labeled(
																label("l2"),
																assign(idexp("netw"), num(21)),
																printS(idexp("netw")))
												)
										),
										archetype(
												"AddServer",
												Collections.singletonList(pcalVarDecl("netw", true, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Arrays.asList(
														pcalVarDecl("a", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
														pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
												),
												Collections.singletonList(
														labeled(
																label("l1"),
																assign(idexp("a"), idexp("netw")),
																assign(idexp("b"), idexp("netw")),
																assign(idexp("netw"), binop("+", idexp("a"), idexp("b")))))
										)
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								Arrays.asList(
										instance(
												pcalVarDecl("S", false, false, num(42)),
												PlusCalFairness.WEAK_FAIR,
												"AddServer",
												Collections.singletonList(ref("network")),
												Collections.singletonList(
														mapping(
																"network",
																"TCPConnection",
																false
														)
												)
										),
										instance(
												pcalVarDecl("C", false, false, num(21)),
												PlusCalFairness.WEAK_FAIR,
												"AddClient",
												Collections.singletonList(ref("network")),
												Collections.singletonList(
														mapping(
																"network",
																"TCPConnection",
																false
														)
												)
										)
								)
						),
						// --algorithm Algorithm5 {
						//     variables network = <<>>;
						//     process (S = 42)
						//     variables a, b, netwRead, netwWrite, netwRead0, netwWrite0, netwWrite1;
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
						//     process (C = 42)
						//     variables netwWrite2, netwRead1, netwWrite3;
						//     {
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
								Collections.singletonList(
										pcalVarDecl("network", false, false, tuple())),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								process(
										pcalVarDecl("S", false, false, num(42)),
										PlusCalFairness.WEAK_FAIR,
										Arrays.asList(
												pcalVarDecl("a", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwWrite1", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
										),
										labeled(
												label("l1"),
												with(
														Collections.singletonList(pcalVarDecl("msg0", false, false, opcall("Head", idexp("network")))),
														assign(idexp("netwWrite"), opcall("Tail", idexp("network"))),
														assign(idexp("netwRead"), idexp("msg0"))),
												assign(idexp("a"), idexp("netwRead")),
												with(
														Collections.singletonList(pcalVarDecl("msg1", false, false, opcall("Head", idexp("netwWrite")))),
														assign(idexp("netwWrite0"), opcall("Tail", idexp("netwWrite"))),
														assign(idexp("netwRead0"), idexp("msg1"))),
												assign(idexp("b"), idexp("netwRead0")),
												assign(idexp("netwWrite1"), opcall("Append", idexp("netwWrite0"), binop("+", idexp("a"), idexp("b")))),
												assign(idexp("network"), idexp("netwWrite1"))
										)
								),
								process(
										pcalVarDecl("C", false, false, num(21)),
										PlusCalFairness.WEAK_FAIR,
										Arrays.asList(
												pcalVarDecl("netwWrite2", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwRead1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwWrite3", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
										),
										labeled(
												label("l1"),
												assign(idexp("netwWrite2"), opcall("Append", idexp("network"), num(21))),
												assign(idexp("network"), idexp("netwWrite2"))
										),
										labeled(
												label("l2"),
												assign(idexp("netwWrite2"), opcall("Append", idexp("network"), num(21))),
												with(
														Collections.singletonList(pcalVarDecl("msg2", false, false, opcall("Head", idexp("netwWrite2")))),
														assign(idexp("netwWrite3"), opcall("Tail", idexp("netwWrite2"))),
														assign(idexp("netwRead1"), idexp("msg2"))),
												printS(idexp("netwRead1")),
												assign(idexp("network"), idexp("netwWrite3"))
										)
								)
						)
				},

				{
						// --mpcal Algorithm6 {
						//   mapping macro FunctionMapping {
						//     read {
						//       yield $variable;
						//     }
						//
						//     write {
						//       yield $value;
						//     }
						//   }
						//
						//   archetype A(ref f)
						//   {
						//       l1: f[0] := 1;
						//           f[1] := 0;
						//           print <<f[0], f[1]>>;
						//   }
						//
						//   variable func = [i \in {0, 1} |-> i];
						//   process (P = 42) == instance A(ref func)
						//   mapping func via FunctionMapping;
						// }
						mpcal(
								"Algorithm6",
								Collections.singletonList(
										pcalVarDecl(
												"func",
												false,
												false,
												function(
														bounds(qbIds(
																Collections.singletonList(id("i")),
																set(num(0), num(1)))),
														idexp("i")))
								),
								Collections.singletonList(
										mappingMacro(
												"Identity",
												Collections.singletonList(yield(DOLLAR_VARIABLE)),
												Collections.singletonList(yield(DOLLAR_VALUE))
										)
								),
								Collections.singletonList(
										archetype(
												"A",
												Collections.singletonList(
														pcalVarDecl("f", true, false, PLUSCAL_DEFAULT_INIT_VALUE)
												),
												Collections.emptyList(),
												Collections.singletonList(
														labeled(
																label("l1"),
																assign(fncall(idexp("f"), num(0)), num(1)),
																assign(fncall(idexp("f"), num(1)), num(0)),
																printS(tuple(fncall(idexp("f"), num(0)), fncall(idexp("f"), num(1)))))))),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										instance(
												pcalVarDecl("P", false, false, num(42)),
												PlusCalFairness.WEAK_FAIR,
												"A",
												Collections.singletonList(ref("func")),
												Collections.singletonList(mapping("func", "Identity", false))
										)
								)
						),
						// --algorithm Algorithm6 {
						//     variables func = [i \in {0,1} |-> i];
						//     process (P = 42)
						//     variables fWrite, fWrite0, fRead, fRead0;
						//     {
						//         l1:
						//             fWrite := [func EXCEPT ![0] = 1];
						//             fWrite0 := [fWrite EXCEPT ![1] = 0];
						//             fRead := fWrite0;
						//             fRead0 := fWrite0;
						//             print <<fRead[0],fRead0[1]>>;
						//             func := fWrite0;
						//     }
						// }
						algorithm(
								"Algorithm6",
								Collections.singletonList(
										pcalVarDecl(
												"func",
												false,
												false,
												function(
														bounds(qbIds(
																Collections.singletonList(id("i")),
																set(num(0), num(1)))),
														idexp("i")))
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								process(
										pcalVarDecl("P", false, false, num(42)),
										PlusCalFairness.WEAK_FAIR,
										Arrays.asList(
												pcalVarDecl("fWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("fWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("fRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("fRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
										),
										labeled(
												label("l1"),
												assign(idexp("fWrite"), fnSubst(idexp("func"), fnSubstPair(Collections.singletonList(substKey(num(0))), num(1)))),
												assign(idexp("fWrite0"), fnSubst(idexp("fWrite"), fnSubstPair(Collections.singletonList(substKey(num(1))), num(0)))),
												assign(idexp("fRead"), idexp("fWrite0")),
												assign(idexp("fRead0"), idexp("fWrite0")),
												printS(tuple(fncall(idexp("fRead"), num(0)), fncall(idexp("fRead0"), num(1)))),
												assign(idexp("func"), idexp("fWrite0"))
										)
								)
						)
				},

				{
						// --mpcal Algorithm7 {
						//   mapping macro TCPConnection {
						//     read {
						//       with (msg = Head($variable)) {
						//         $variable := Tail($variable);
						//         yield msg;
						//       }
						//     }
						//
						//     write {
						//       yield Append($variable, $value);
						//     }
						//   }
						//
						//   archetype AddClient(ref netw) {
						//       l1: netw[self] := 21;
						//       l2: netw[self] := 21;
						//           print netw[self];
						//   }
						//
						//   archetype AddServer(ref netw)
						//   variables a, b, dest;
						//   {
						//       l1: either {
						//             a := netw[0];
						//             dest := 0;
						//           } or {
						//             a := netw[1];
						//             dest := 1;
						//           }
						//           b := netw[dest];
						//           netw[dest] := a + b;
						//   }
						//
						//   variable network = [i \in {0, 1} |-> <<>>];
						//   process (S = 42) == instance AddServer(ref network)
						//   mapping network[_] via TCPConnection;
						//   process (C \in {0, 1}) == instance AddClient(ref network)
						//   mapping network[_] via TCPConnection;
						// }
						mpcal(
								"Algorithm7",
								Collections.singletonList(
										pcalVarDecl(
												"network",
												false,
												false,
												function(bounds(qbIds(Collections.singletonList(id("i")), set(num(0), num(1)))), tuple()))
								),
								Collections.singletonList(
										mappingMacro(
												"TCPConnection",
												Collections.singletonList(
														with(
																Collections.singletonList(pcalVarDecl("msg", false, false, opcall("Head", DOLLAR_VARIABLE))),
																assign(DOLLAR_VARIABLE, opcall("Tail", DOLLAR_VARIABLE)),
																yield(idexp("msg")))
												),
												Collections.singletonList(
														yield(opcall("Append", DOLLAR_VARIABLE, DOLLAR_VALUE))
												)
										)
								),
								Arrays.asList(
										archetype(
												"AddClient",
												Collections.singletonList(pcalVarDecl("netw", true, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Collections.emptyList(),
												Arrays.asList(
														labeled(
																label("l1"),
																assign(fncall(idexp("netw"), idexp("self")), num(21))),
														labeled(
																label("l2"),
																assign(fncall(idexp("netw"), idexp("self")), num(21)),
																printS(fncall(idexp("netw"), idexp("self"))))
												)
										),
										archetype(
												"AddServer",
												Collections.singletonList(pcalVarDecl("netw", true, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Arrays.asList(
														pcalVarDecl("a", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
														pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
														pcalVarDecl("dest", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
												),
												Collections.singletonList(
														labeled(
																label("l1"),
																either(Arrays.asList(
																		Arrays.asList(
																				assign(idexp("a"), fncall(idexp("netw"), num(0))),
																				assign(idexp("dest"), num(0))
																		),
																		Arrays.asList(
																				assign(idexp("a"), fncall(idexp("netw"), num(1))),
																				assign(idexp("dest"), num(1))
																		)
																)),
																assign(idexp("b"), fncall(idexp("netw"), idexp("dest"))),
																assign(fncall(idexp("netw"), idexp("dest")), binop("+", idexp("a"), idexp("b")))))
										)
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								Arrays.asList(
										instance(
												pcalVarDecl("S", false, false, num(42)),
												PlusCalFairness.WEAK_FAIR,
												"AddServer",
												Collections.singletonList(ref("network")),
												Collections.singletonList(
														mapping(
																"network",
																"TCPConnection",
																true
														)
												)
										),
										instance(
												pcalVarDecl("C", false, true, set(num(0), num(1))),
												PlusCalFairness.WEAK_FAIR,
												"AddClient",
												Collections.singletonList(ref("network")),
												Collections.singletonList(
														mapping(
																"network",
																"TCPConnection",
																true
														)
												)
										)
								)
						),
						// --algorithm Algorithm7 {
						//     variables network = [i \in {0,1}|-><<>>];
						//     process (S = 42)
						//     variables a, b, dest, netwRead, netwWrite, netwRead0, netwWrite0, netwRead1, netwWrite1, netwWrite2;
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
						//     process (C \in {0,1})
						//     variables netwWrite3, netwRead2, netwWrite4;
						//     {
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
								Collections.singletonList(
										pcalVarDecl(
												"network",
												false,
												false,
												function(bounds(qbIds(Collections.singletonList(id("i")), set(num(0), num(1)))), tuple()))
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								process(
										pcalVarDecl("S", false, false, num(42)),
										PlusCalFairness.WEAK_FAIR,
										Arrays.asList(
												pcalVarDecl("a", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("dest", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwWrite", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwWrite0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwRead1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwWrite1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwWrite2", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
										),
										labeled(
												label("l1"),
												either(Arrays.asList(
														Arrays.asList(
																with(
																		Collections.singletonList(pcalVarDecl("msg0", false, false, opcall("Head", fncall(idexp("network"), num(0))))),
																		assign(idexp("netwWrite"), fnSubst(idexp("network"), fnSubstPair(Collections.singletonList(substKey(num(0))), opcall("Tail", fncall(idexp("network"), num(0)))))),
																		assign(idexp("netwRead"), idexp("msg0"))),
																assign(idexp("a"), idexp("netwRead")),
																assign(idexp("dest"), num(0)),
																assign(idexp("netwWrite0"), idexp("netwWrite"))
														),
														Arrays.asList(
																with(
																		Collections.singletonList(pcalVarDecl("msg1", false, false, opcall("Head", fncall(idexp("network"), num(1))))),
																		assign(idexp("netwWrite"), fnSubst(idexp("network"), fnSubstPair(Collections.singletonList(substKey(num(1))), opcall("Tail", fncall(idexp("network"), num(1)))))),
																		assign(idexp("netwRead0"), idexp("msg1"))),
																assign(idexp("a"), idexp("netwRead0")),
																assign(idexp("dest"), num(1)),
																assign(idexp("netwWrite0"), idexp("netwWrite"))
														)
												)),
												with(
														Collections.singletonList(pcalVarDecl("msg2", false, false, opcall("Head", fncall(idexp("netwWrite0"), idexp("dest"))))),
														assign(idexp("netwWrite1"), fnSubst(idexp("netwWrite0"), fnSubstPair(Collections.singletonList(substKey(idexp("dest"))), opcall("Tail", fncall(idexp("netwWrite0"), idexp("dest")))))),
														assign(idexp("netwRead1"), idexp("msg2"))),
												assign(idexp("b"), idexp("netwRead1")),
												assign(idexp("netwWrite2"), fnSubst(idexp("netwWrite1"), fnSubstPair(Collections.singletonList(substKey(idexp("dest"))), opcall("Append", fncall(idexp("netwWrite1"), idexp("dest")), binop("+", idexp("a"), idexp("b")))))),
												assign(idexp("network"), idexp("netwWrite2"))
										)
								),
								process(
										pcalVarDecl("C", false, true, set(num(0), num(1))),
										PlusCalFairness.WEAK_FAIR,
										Arrays.asList(
												pcalVarDecl("netwWrite3", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwRead2", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
												pcalVarDecl("netwWrite4", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
										),
										labeled(
												label("l1"),
												assign(idexp("netwWrite3"), fnSubst(idexp("network"), fnSubstPair(Collections.singletonList(substKey(idexp("self"))), opcall("Append", fncall(idexp("network"), idexp("self")), num(21))))),
												assign(idexp("network"), idexp("netwWrite3"))
										),
										labeled(
												label("l2"),
												assign(idexp("netwWrite3"), fnSubst(idexp("network"), fnSubstPair(Collections.singletonList(substKey(idexp("self"))), opcall("Append", fncall(idexp("network"), idexp("self")), num(21))))),
												with(
														Collections.singletonList(pcalVarDecl("msg3", false, false, opcall("Head", fncall(idexp("netwWrite3"), idexp("self"))))),
														assign(idexp("netwWrite4"), fnSubst(idexp("netwWrite3"), fnSubstPair(Collections.singletonList(substKey(idexp("self"))), opcall("Tail", fncall(idexp("netwWrite3"), idexp("self")))))),
														assign(idexp("netwRead2"), idexp("msg3"))),
												printS(idexp("netwRead2")),
												assign(idexp("network"), idexp("netwWrite4"))
										)
								)
						)
				},
		});
	}

	private static final Path testFile = Paths.get("TEST");
	private static final TLAIdentifier moduleName = id("TestModule");

	private ModularPlusCalBlock before;
	private PlusCalAlgorithm expected;

	public PlusCalCodeGenPassTest(ModularPlusCalBlock before, PlusCalAlgorithm expected) {
		this.before = before;
		this.expected = expected;
	}

	@Test
	public void test() throws PGoTransException  {
		PGoMain main = new PGoMain(new String[1]);
		TopLevelIssueContext ctx = new TopLevelIssueContext();
		TLAModule tlaModule = new TLAModule(
				SourceLocation.unknown(),
				moduleName,
				Arrays.asList(id("Integers"), id("Sequences")),
				Collections.emptyList(),
				Collections.emptyList(),
				Collections.emptyList());

		PlusCalAlgorithm after = main.mpcalToPcal(testFile, ctx, before, tlaModule);
		assertThat(after, is(expected));
	}

}