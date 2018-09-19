package pgo.trans.intermediate;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.errors.TopLevelIssueContext;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.*;
import pgo.model.tla.TLABool;
import pgo.trans.passes.mpcal.ModularPlusCalValidationPass;

import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.mpcal.ModularPlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class ModularPlusCalValidationTest {

    @Parameters
    public static List<Object[]> data() {
        return Arrays.asList(new Object[][] {
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
                {
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

                // --mpcal ArchetypeNoFirstLabel {
                //     archetype MyArchetype() {
                //         print(1 + 1);
                //     }
                // }
                {
                        mpcal(
                                "ArchetypeNoFirstLabel",
                                Collections.singletonList(
                                        archetype(
                                                "MyArchetype",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                Collections.singletonList(
                                                        printS(binop("+", num(1), num(1)))
                                                )
                                        )
                                ),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList()
                        ),
                        Collections.singletonList(
                                new InvalidModularPlusCalIssue(
                                        InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                        printS(binop("+", num(1), num(1)))
                                )
                        ),
                },

                // --mpcal ProcedureNoFirstLabel {
                //     procedure MyProcess() {
                //         print(1 + 1);
                //     }
                // }
                {
                        mpcal(
                                "ProcedureNoFirstLabel",
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.singletonList(
                                        procedure(
                                                "MyProcedure",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                printS(binop("+", num(1), num(1)))
                                        )
                                ),
                                Collections.emptyList()
                        ),
                        Collections.singletonList(
                                new InvalidModularPlusCalIssue(
                                        InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                        printS(binop("+", num(1), num(1)))
                                )
                        ),
                },

                // --mpcal ProcessNoFirstLabel {
                //     process MyProcess() {
                //         print(1 + 1);
                //     }
                // }
                {
                        mpcal(
                                "ProcessNoFirstLabel",
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                process(
                                        pcalVarDecl("MyProcess", false, false, num(32)),
                                        PlusCalFairness.WEAK_FAIR,
                                        Collections.emptyList(),
                                        printS(binop("+", num(1), num(1)))
                                )

                        ),
                        Collections.singletonList(
                                new InvalidModularPlusCalIssue(
                                        InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                        printS(binop("+", num(1), num(1)))
                                )
                        ),
                },

                // --mpcal MoreThanOneIssue {
                //     archetype ValidArchetype() {
                //         l1: print(1 + 1);
                //     }
                //
                //     archetype InvalidArchetype() {
                //         print("invalid archetype!");
                //     }
                //
                //     procedure ValidProcedure() {
                //         l2: print(3 - 3);
                //     }
                //
                //     procedure InvalidProcedure() {
                //         print("invalid procedure!");
                //     }
                //
                //     process (ValidProcess = 32) {
                //         l3: print(2 * 2);
                //     }
                //
                //     process (InvalidProcess = 64) {
                //         print("invalid process!");
                //     }
                // }
                {
                        mpcal(
                                "MoreThanOneIssue",
                                new ArrayList<ModularPlusCalArchetype>() {{
                                    add(
                                            archetype(
                                                    "ValidArchetype",
                                                    Collections.emptyList(),
                                                    Collections.emptyList(),
                                                    Collections.singletonList(
                                                            labeled(
                                                                    label("l1"),
                                                                    printS(binop("+",num(1), num(1)))
                                                            )
                                                    )
                                            )
                                    );
                                    add(
                                            archetype(
                                                    "InvalidArchetype",
                                                    Collections.emptyList(),
                                                    Collections.emptyList(),
                                                    Collections.singletonList(
                                                            printS(str("invalid archetype!"))
                                                    )
                                            )
                                    );
                                }},
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                new ArrayList<PlusCalProcedure>() {{
                                    add(
                                            procedure(
                                                    "ValidProcedure",
                                                    Collections.emptyList(),
                                                    Collections.emptyList(),
                                                    labeled(
                                                            label("l2"),
                                                            printS(binop("-", num(3), num(3)))
                                                    )
                                            )
                                    );
                                    add(
                                            procedure(
                                                    "InvalidProcedure",
                                                    Collections.emptyList(),
                                                    Collections.emptyList(),
                                                    printS(str("invalid procedure!"))
                                            )
                                    );
                                }},
                                Collections.emptyList(),
                                process(
                                        pcalVarDecl("ValidProcess", false, false, num(32)),
                                        PlusCalFairness.WEAK_FAIR,
                                        Collections.emptyList(),
                                        labeled(
                                                label("l3"),
                                                printS(binop("*", num(2), num(2)))
                                        )
                                ),
                                process(
                                        pcalVarDecl("InvalidProcess", false, false, num(64)),
                                        PlusCalFairness.WEAK_FAIR,
                                        Collections.emptyList(),
                                        printS(str("invalid process!"))
                                )
                        ),
                        new ArrayList<InvalidModularPlusCalIssue>() {{
                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            printS(str("invalid archetype!"))
                                    )
                            );
                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            printS(str("invalid procedure!"))
                                    )
                            );
                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            printS(str("invalid process!"))
                                    )
                            );
                        }},
                },

                // --mpcal WhileLabels {
                //     archetype IncorrectArchetype() {
                //         l1: print "first label";
                //         while (TRUE) { print "hello" }; (* missing label here *)
                //     }
                //
                //     procedure CorrectProcedure() {
                //         l2: print "procedure";
                //         l3: while (FALSE) { print(3 - 3) }; (* all good *)
                //     }
                //
                //     process (IncorrectProcess = 32) {
                //         while (10 < 20) { print(2 * 2) }; (* missing label (first statement) *)
                //     }
                // }
                {
                        mpcal(
                                "WhileLabels",
                                Collections.singletonList(
                                        archetype(
                                                "IncorrectArchetype",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                new ArrayList<PlusCalStatement>() {{
                                                    add(
                                                            labeled(label("l1"),
                                                                    printS(str("first label")))
                                                    );

                                                    add(
                                                            whileS(bool(true), Collections.singletonList(
                                                                    printS(str("hello"))
                                                            ))
                                                    );
                                                }}
                                        )
                                ),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.singletonList(
                                        procedure(
                                                "CorrectProcedure",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                labeled(label("l2"), printS(str("procedure"))),
                                                labeled(label("l3"), whileS(bool(false), Collections.singletonList(
                                                        printS(binop("-", num(3), num(3))))))
                                        )
                                ),
                                Collections.emptyList(),
                                process(
                                        pcalVarDecl("IncorrectProcess", false, false, num(32)),
                                        PlusCalFairness.WEAK_FAIR,
                                        Collections.emptyList(),
                                        whileS(binop("<", num(10), num(20)), Collections.singletonList(
                                                printS(binop("*", num(2), num(2))))
                                        )
                                )
                        ),
                        new ArrayList<InvalidModularPlusCalIssue>() {{
                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            whileS(bool(true), Collections.singletonList(
                                                    printS(str("hello"))
                                            ))
                                    )
                            );

                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            whileS(binop("<", num(10), num(20)), Collections.singletonList(
                                                    printS(binop("*", num(2), num(2))))
                                            )
                                    )
                            );
                        }},
                },
                // --mpcal CallLabelingRules {
                //     archetype MyArchetype() {
                //         l1: print "first label";
                //         call MyProcedure();
                //         call MyProcedure(); (* missing label *)
                //     }
                //
                //     procedure MyProcedure() {
                //         l2: print "procedure";
                //         call SomeProcedure();
                //         return; (* no label required *)
                //     }
                //
                //     process (MyProcess = 32) {
                //         l3: print "process";
                //         call MyProcedure();
                //         goto l3; (* no label required *)
                //         l4: print "next label";
                //         call MyProcedure();
                //         x := 10; (* missing label *)
                //     }
                // }
                {
                        mpcal(
                                "CallLabelingRules",
                                Collections.singletonList(
                                        archetype(
                                                "MyArchetype",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                new ArrayList<PlusCalStatement>() {{
                                                    add(
                                                            labeled(label("l1"),
                                                                    printS(str("first label")))
                                                    );

                                                    add(call("MyProcedure"));
                                                    add(call("MyProcedure"));
                                                }}
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
                                                labeled(label("l2"), printS(str("procedure"))),
                                                call("SomeProcedure"),
                                                returnS()
                                        )
                                ),
                                Collections.emptyList(),
                                process(
                                        pcalVarDecl("MyProcess", false, false, num(32)),
                                        PlusCalFairness.WEAK_FAIR,
                                        Collections.emptyList(),
                                        labeled(label("l3"), printS(str("process"))),
                                        call("MyProcedure"),
                                        gotoS("l3"),
                                        labeled(label("l4"), printS(str("next label"))),
                                        call("MyProcedure"),
                                        assign(idexp("x"), num(10))
                                )
                        ),
                        new ArrayList<InvalidModularPlusCalIssue>() {{
                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            call("MyProcedure")
                                    )
                            );

                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            assign(idexp("x"), num(10))
                                    )
                            );
                        }},
                },
                // --mpcal ReturnGotoLabelingRules {
                //     archetype MyArchetype() {
                //         l1: print "first label";
                //         goto l1;
                //         print "needs label"; (* missing label *)
                //     }
                //
                //     procedure MyProcedure() {
                //         l2: print "procedure";
                //         return;
                //         goto l2; (* missing label *)
                //     }
                //
                //     process (MyProcess = 32) {
                //         l3: print "process";
                //         goto l3;
                //         x := 10; (* missing label *)
                //     }
                // }
                {
                        mpcal(
                                "ReturnGotoLabelingRules",
                                Collections.singletonList(
                                        archetype(
                                                "MyArchetype",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                new ArrayList<PlusCalStatement>() {{
                                                    add(
                                                            labeled(label("l1"),
                                                                    printS(str("first label")))
                                                    );

                                                    add(gotoS("l1"));
                                                    add(printS(str("needs label")));
                                                }}
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
                                                labeled(label("l2"), printS(str("procedure"))),
                                                returnS(),
                                                gotoS("l2")
                                        )
                                ),
                                Collections.emptyList(),
                                process(
                                        pcalVarDecl("MyProcess", false, false, num(32)),
                                        PlusCalFairness.WEAK_FAIR,
                                        Collections.emptyList(),
                                        labeled(label("l3"), printS(str("process"))),
                                        gotoS("l3"),
                                        assign(idexp("x"), num(10))
                                )
                        ),
                        new ArrayList<InvalidModularPlusCalIssue>() {{
                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            printS(str("needs label"))
                                    )
                            );

                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            gotoS("l2")
                                    )
                            );

                            add(
                                    new InvalidModularPlusCalIssue(
                                            InvalidModularPlusCalIssue.InvalidReason.MISSING_LABEL,
                                            assign(idexp("x"), num(10))
                                    )
                            );
                        }},
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
