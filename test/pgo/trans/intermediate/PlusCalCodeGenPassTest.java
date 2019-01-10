package pgo.trans.intermediate;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.pcal.PlusCalFairness;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.trans.passes.codegen.pluscal.PlusCalCodeGenPass;

import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;
import static pgo.model.mpcal.ModularPlusCalBuilder.*;


@RunWith(Parameterized.class)
public class PlusCalCodeGenPassTest {

    @Parameters
    public static List<Object[]> testCases(){
        return Arrays.asList(new Object[][] {
                // -- mpcal Algorithm1 {
                //     archetype A1(x) {
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
                                                        pcalVarDecl("x", false, false, PLUSCAL_DEFAULT_INIT_VALUE)
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
        });
    }

    private ModularPlusCalBlock before;
    private PlusCalAlgorithm expected;

    public PlusCalCodeGenPassTest(ModularPlusCalBlock before, PlusCalAlgorithm expected) {
        this.before = before;
        this.expected = expected;
    }

    @Test
    public void test() {
        IssueContext ctx = new TopLevelIssueContext();
        DefinitionRegistry registry = new DefinitionRegistry();

        for (PlusCalProcedure procedure : before.getProcedures()) {
            registry.addProcedure(procedure);
        }

        for (PlusCalVariableDeclaration variable : before.getVariables()) {
            registry.addGlobalVariable(variable.getUID());
        }

        for (ModularPlusCalArchetype archetype : before.getArchetypes()) {
            registry.addArchetype(archetype);
        }

        PlusCalAlgorithm after = PlusCalCodeGenPass.perform(ctx, registry, before);
        assertThat(after, is(expected));
    }

}