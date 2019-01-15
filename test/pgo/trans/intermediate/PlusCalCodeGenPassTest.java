package pgo.trans.intermediate;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.PGoMain;
import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.pcal.PlusCalFairness;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAIdentifier;
import pgo.model.tla.TLAModule;
import pgo.trans.PGoTransException;
import pgo.trans.passes.codegen.pluscal.PlusCalCodeGenPass;
import pgo.trans.passes.parse.tla.TLAParsingPass;
import pgo.util.SourceLocation;

import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;
import static pgo.model.mpcal.ModularPlusCalBuilder.*;


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
                    //             y := bRead;
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
                                            printS(tuple(idexp("aRead"), idexp("bRead"))),
                                            assign(idexp("y"), idexp("bRead"))
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
                    //            };
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
                        //    process (P1 = 42)
                        //    variables local, aRead, aRead0, bRead;
                        //    {
                        //        l1:
                        //            x := (x)-(1);
                        //            with (v = 50) {
                        //                either {
                        //                    aRead := v;
                        //                } or {
                        //                    aRead := 10;
                        //                }
                        //            };
                        //            if ((aRead)>=(42)) {
                        //                local := 42;
                        //                };
                        //        l2:
                        //            x := (10)+(1);
                        //        l3:
                        //            x := (x)-(1);
                        //            with (v = 50) {
                        //                either {
                        //                    aRead0 := v;
                        //                } or {
                        //                    aRead0 := 10;
                        //                }
                        //            };
                        //            bRead := y;
                        //            local := (aRead0)+(bRead);
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
                                        pcalVarDecl("P1", false, false, num(42)),
                                        PlusCalFairness.WEAK_FAIR,
                                        Arrays.asList(
                                                pcalVarDecl("local", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
                                                pcalVarDecl("aRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
                                                pcalVarDecl("aRead0", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
                                                pcalVarDecl("bRead", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
                                        ),
                                        labeled(
                                                label("l1"),
                                                assign(idexp("x"), binop("-", idexp("x"), num(1))),
                                                with(
                                                        Collections.singletonList(pcalVarDecl("v", false, false, num(50))),
                                                        either(
                                                                Arrays.asList(
                                                                        Collections.singletonList(assign(idexp("aRead"), idexp("v"))),
                                                                        Collections.singletonList(assign(idexp("aRead"), num(10)))
                                                                )
                                                        )
                                                ),
                                                ifS(
                                                        binop(">=", idexp("a"), num(42)),
                                                        Collections.singletonList(assign(idexp("local"), num(42))),
                                                        Collections.emptyList()
                                                )
                                        ),

                                        labeled(
                                                label("l2"),
                                                assign(idexp("x"), binop("+", num(10), num(1)))
                                        ),

                                        labeled(
                                                label("l3"),
                                                assign(idexp("x"), binop("-", idexp("x"), num(1))),
                                                with(
                                                        Collections.singletonList(pcalVarDecl("v", false, false, num(50))),
                                                        either(
                                                                Arrays.asList(
                                                                        Collections.singletonList(assign(idexp("aRead0"), idexp("v"))),
                                                                        Collections.singletonList(assign(idexp("aRead0"), num(10)))
                                                                )
                                                        )
                                                ),
                                                assign(idexp("bRead"), idexp("y")),
                                                assign(idexp("local"), binop("+", idexp("aRead0"), idexp("bRead")))
                                        ),

                                        labeled(
                                                label("l4"),
                                                printS(idexp("local"))
                                        )
                                )
                        )
                }
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
                Collections.singletonList(id("Integers")),
                Collections.emptyList(),
                Collections.emptyList(),
                Collections.emptyList());

        PlusCalAlgorithm after = main.mpcalToPcal(testFile, ctx, before, tlaModule);
        assertThat(after, is(expected));
    }

}