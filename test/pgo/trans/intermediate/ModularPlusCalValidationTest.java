package pgo.trans.intermediate;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.errors.TopLevelIssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalFairness;
import pgo.model.pcal.PlusCalLabel;
import pgo.model.pcal.PlusCalLabeledStatements;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLANumber;
import pgo.parser.Located;
import pgo.trans.passes.mpcal.ModularPlusCalValidationPass;
import pgo.util.SourceLocation;

import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class ModularPlusCalValidationTest {

    @Parameters
    public static List<Object[]> data(){
        return Arrays.asList(new Object[][] {
                {
                    // (**
                    // --mpcal NoIssues {
                    //     archetype MyArchetype() {
                    //         l1: print(1 + 1);
                    //     }
                    //
                    //     procedure MyProcedure() {
                    //         l2: print(3 - 3);
                    //     }
                    //
                    //     process (MyProcess = 32) {
                    //         l3: print(2 * 2);
                    //     }
                    // }
                    //
                    mpcal(
                        "NoIssues",
                        Collections.singletonList(
                            archetype(
                                    "MyArchetype",
                                    Collections.emptyList(),
                                    Collections.emptyList(),
                                    Collections.singletonList(
                                            labeled(label("l1"), printS(binop("+", num(1), num(1))))
                                    )
                            )
                        ),
                        Collections.emptyList(),
                        Collections.emptyList(),
                        Collections.emptyList(),
                        Collections.emptyList(),
                        Collections.singletonList(
                                procedure(
                                        "MyProcedure",
                                        Collections.emptyList(),
                                        Collections.emptyList(),
                                        labeled(label("l2"), printS(binop("-", num(3), num(3))))
                                )
                        ),
                        Collections.emptyList(),
                        process(
                                    pcalVarDecl("MyProcess", false, false, num(32)),
                                    PlusCalFairness.WEAK_FAIR,
                                    Collections.emptyList(),
                                    labeled(
                                        label("l3"),
                                        printS(binop("*", num(2), num(2)))
                                    )
                        )

                    ),
                    Collections.emptyList(),
                },
        });
    }

    private ModularPlusCalBlock spec;
    private List<InvalidModularPlusCalIssue> issues;

    public ModularPlusCalValidationTest(ModularPlusCalBlock spec, List<InvalidModularPlusCalIssue> issues) {
        this.spec = spec;
        this.issues = issues;
    }

    @Test
    public void test() {
        TopLevelIssueContext ctx = new TopLevelIssueContext();
        ModularPlusCalValidationPass.perform(ctx, spec);

        assertEquals(issues, ctx.getIssues());
    }

}
