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
                }
        });
    }

    private static final Path testFile = Paths.get("TEST");
    private static final TLAIdentifier moduleName = id("testModule");

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
                Collections.emptyList(),
                Collections.emptyList(),
                Collections.emptyList(),
                Collections.emptyList());

        PlusCalAlgorithm after = main.mpcalToPcal(testFile, ctx, before, tlaModule);
        assertThat(after, is(expected));
    }

}