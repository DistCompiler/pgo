package pgo.trans.intermediate;

import static org.junit.Assert.*;

import java.util.*;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.errors.Issue;
import pgo.errors.TopLevelIssueContext;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.*;
import pgo.trans.passes.mpcal.ModularPlusCalValidationPass;

import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.mpcal.ModularPlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class ModularPlusCalLabelingRulesTest {

    @Parameters
    public static List<Object[]> data() {
        return Arrays.asList(new Object[][] {
                // --mpcal NoIssues {
                //     archetype MyArchetype() {
                //         l1: print(1 + 1);
                //         l2: either { x := 10 } or { x := 20 };
                //     }
                //
                //     procedure MyProcedure() {
                //         l2: print(3 - 3);
                //             if (TRUE) {
                //                 y := 20;
                //             } else {
                //                 y := 10;
                //             }
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
                                    new ArrayList<PlusCalStatement>() {{
                                        add(labeled(
                                                label("l1"),
                                                printS(binop("+", num(1), num(1))))
                                        );

                                        add(labeled(
                                                label("l2"),
                                                either(new ArrayList<List<PlusCalStatement>>() {{
                                                    add(Collections.singletonList(
                                                            assign(idexp("x"), num(10))
                                                    ));

                                                    add(Collections.singletonList(
                                                            assign(idexp("x"), num(20))
                                                    ));
                                                }})
                                        ));
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
                                        labeled(
                                                label("l2"),
                                                printS(binop("-", num(3), num(3))),
                                                ifS(
                                                        bool(true),
                                                        Collections.singletonList(
                                                                assign(idexp("y"), num(10))
                                                        ),
                                                        Collections.singletonList(
                                                                assign(idexp("y"), num(20))
                                                        )
                                                )
                                        )
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
                                new MissingLabelIssue(printS(binop("+", num(1), num(1))))
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
                                new MissingLabelIssue(printS(binop("+", num(1), num(1))))
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
                                new MissingLabelIssue(printS(binop("+", num(1), num(1))))
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
                        new ArrayList<Issue>() {{
                            add(new MissingLabelIssue(printS(str("invalid archetype!"))));
                            add(new MissingLabelIssue(printS(str("invalid procedure!"))));
                            add(new MissingLabelIssue(printS(str("invalid process!"))));
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
                        new ArrayList<Issue>() {{
                            add(
                                    new MissingLabelIssue(
                                            whileS(bool(true), Collections.singletonList(
                                                    printS(str("hello"))
                                            ))
                                    )
                            );

                            add(
                                    new MissingLabelIssue(
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
                        new ArrayList<Issue>() {{
                            add(new MissingLabelIssue(call("MyProcedure")));
                            add(new MissingLabelIssue(assign(idexp("x"), num(10))));
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
                        new ArrayList<Issue>() {{
                            add(new MissingLabelIssue(printS(str("needs label"))));
                            add(new MissingLabelIssue(gotoS("l2")));
                            add(new MissingLabelIssue(assign(idexp("x"), num(10))));
                        }},
                },

                // --mpcal IfEitherLabelingRules {
                //     archetype MyArchetype() {
                //         l1: print "first label";
                //         if (TRUE) {
                //             print "true";
                //         } else if (TRUE) {
                //             call MyProcedure();
                //         }
                //
                //         print "needs label"; (* missing label *)
                //     }
                //
                //     procedure MyProcedure() {
                //         l2: print "procedure";
                //         either { v := 10 } or { return };
                //         goto l2; (* missing label *)
                //     }
                //
                //     process (MyProcess = 32) {
                //         l3: print "process";
                //         either { x := 0 } or { goto l3 };
                //         l4: print "all good";
                //
                //         either { goto l4 } or { skip };
                //         x := 50; (* missing label *)
                //
                //         l5: if (TRUE) {
                //                 l6: print "label";
                //             }
                //         y := 20; (* missing label *)
                //     }
                // }
                {
                        mpcal(
                                "IfEitherLabelingRules",
                                Collections.singletonList(
                                        archetype(
                                                "MyArchetype",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                new ArrayList<PlusCalStatement>() {{
                                                    add(
                                                            labeled(label("l1"),
                                                                    printS(str("first label")),
                                                                    ifS(bool(true), Collections.singletonList(
                                                                            printS(str("true"))
                                                                    ), Collections.singletonList(
                                                                            ifS(bool(true), Collections.singletonList(
                                                                                    call("MyProcedure")
                                                                            ), Collections.emptyList())
                                                                    ))
                                                            )
                                                    );
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
                                                labeled(label("l2"),
                                                        printS(str("procedure")),
                                                        either(new ArrayList<List<PlusCalStatement>>() {{
                                                            add(Collections.singletonList(
                                                                    assign(idexp("v"), num(10))
                                                            ));

                                                            add(Collections.singletonList(
                                                                    returnS()
                                                            ));
                                                        }}),
                                                        gotoS("l2"))
                                        )
                                ),
                                Collections.emptyList(),
                                process(
                                        pcalVarDecl("MyProcess", false, false, num(32)),
                                        PlusCalFairness.WEAK_FAIR,
                                        Collections.emptyList(),
                                        labeled(label("l3"), printS(str("process"))),
                                        either(new ArrayList<List<PlusCalStatement>>() {{
                                            add(Collections.singletonList(
                                                    assign(idexp("x"), num(0))
                                            ));

                                            add(Collections.singletonList(
                                                    gotoS("l3")
                                            ));
                                        }}),
                                        labeled(label("l4"), printS(str("all good"))),
                                        either(new ArrayList<List<PlusCalStatement>>() {{
                                            add(Collections.singletonList(
                                                    gotoS("l4")
                                            ));

                                            add(Collections.singletonList(
                                                    skip()
                                            ));
                                        }}),
                                        assign(idexp("x"), num(50)),
                                        labeled(label("l5"), ifS(bool(true), Collections.singletonList(
                                                labeled(label("l6"), printS(str("label")))
                                        ), Collections.emptyList())),
                                        assign(idexp("y"), num(20))
                                )
                        ),
                        new ArrayList<Issue>() {{
                            add(new MissingLabelIssue(printS(str("needs label"))));
                            add(new MissingLabelIssue(gotoS("l2")));
                            add(new MissingLabelIssue(assign(idexp("x"), num(50))));
                            add(new MissingLabelIssue(assign(idexp("y"), num(20))));
                        }},
                },

                // --mpcal MacroRules {
                //     macro ValidMacro() {
                //         print(1 + 1);
                //         x := 10;
                //     }
                //
                //     macro InvalidMacro() {
                //         either { skip } or { l1: y := 10 }; (* invalid *)
                //         l2: y := 20; (* invalid *)
                //     }
                // }
                {
                        mpcal(
                                "MacroRules",
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                new ArrayList<PlusCalMacro>() {{
                                    add(macro(
                                            "ValidMacro",
                                            Collections.emptyList(),
                                            printS(binop("+", num(1), num(1))),
                                            assign(idexp("x"), num(10))
                                    ));

                                    add(macro(
                                            "InvalidMacro",
                                            Collections.emptyList(),
                                            either(new ArrayList<List<PlusCalStatement>>() {{
                                                add(Collections.singletonList(skip()));
                                                add(Collections.singletonList(
                                                        labeled(label("l1"), assign(idexp("y"), num(10)))
                                                ));
                                            }}),
                                            labeled(label("l2"), assign(idexp("y"), num(20)))
                                    ));
                                }},
                                Collections.emptyList(),
                                Collections.emptyList()
                        ),
                        new ArrayList<Issue>() {{
                            add(new LabelNotAllowedIssue(labeled(label("l1"), assign(idexp("y"), num(10)))));
                            add(new LabelNotAllowedIssue(labeled(label("l2"), assign(idexp("y"), num(20)))));
                        }},
                },

                // --mpcal WithRules {
                //     macro MacroWith() {
                //         print(1 + 1);
                //         with (x = 10) {
                //             print x;
                //             m1: x := 20; (* invalid *)
                //         }
                //         m2: y := 20; (* invalid *)
                //     }
                //
                //     procedure ProcedureWith() {
                //         l1: with (x = 10) {
                //                 l2: print x; (* invalid *)
                //             }
                //     }
                // }
                {
                        mpcal(
                                "WithRules",
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.emptyList(),
                                Collections.singletonList(
                                        macro(
                                                "MacroWith",
                                                Collections.emptyList(),
                                                printS(binop("+", num(1), num(1))),
                                                with(
                                                        Collections.singletonList(
                                                                pcalVarDecl("x", false, false, num(10))
                                                        ),
                                                        printS(idexp("x")),
                                                        labeled(label("m1"), assign(idexp("x"), num(20)))
                                                ),
                                                labeled(label("m2"), assign(idexp("y"), num(20)))
                                        )
                                ),
                                Collections.singletonList(
                                        procedure(
                                                "ProcedureWith",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                labeled(label("l1"), with(
                                                        Collections.singletonList(
                                                                pcalVarDecl("x", false, false, num(10))
                                                        ),
                                                        labeled(label("l2"), printS(idexp("x")))
                                                ))
                                        )
                                ),
                                Collections.emptyList()
                        ),
                        new ArrayList<Issue>() {{
                            add(new LabelNotAllowedIssue(labeled(label("m1"), assign(idexp("x"), num(20)))));
                            add(new LabelNotAllowedIssue(labeled(label("m2"), assign(idexp("y"), num(20)))));
                            add(new LabelNotAllowedIssue(labeled(label("l2"), printS(idexp("x")))));
                        }},
                },
                // --mpcal AssignmentRules {
                //     archetype MyArchetype() {
                //         a1: x := 10;
                //         x := 11; (* missing label *)
                //     }
                //
                //     procedure MyProcedure() {
                //         p: either { y := 10 } or { skip };
                //            y := 11; (* missing label *)
                //         p2: y := 20;
                //             x := y || y := x; (* swap x and y: invalid *)
                //     }
                //
                //     process (MyProcess = 23) {
                //         l1: n := 2;
                //         l2: while (n < 10) {
                //             n := 12;
                //             if (n := 20) {
                //                 n := 100; (* missing label *)
                //             }
                //         };
                //         n := 32; (* label not missing *)
                //
                //         l3: if (n = 32) {
                //             n := 0;
                //         };
                //         n := 12; (* missing label *)
                //     }
                // }
                {
                        mpcal(
                                "AssignmentRules",
                                Collections.singletonList(
                                        archetype(
                                                "MyArchetype",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                new ArrayList<PlusCalStatement>() {{
                                                    add(
                                                            labeled(
                                                                    label("a1"),
                                                                    assign(idexp("x"), num(10)),
                                                                    assign(idexp("x"), num(11))
                                                    ));
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
                                                labeled(
                                                        label("p"),
                                                        either(new ArrayList<List<PlusCalStatement>>() {{
                                                            add(Collections.singletonList(
                                                                    assign(idexp("y"), num(10))
                                                            ));

                                                            add(Collections.singletonList(skip()));
                                                        }}),
                                                        assign(idexp("y"), num(11))
                                                ),
                                                labeled(
                                                        label("p2"),
                                                        assign(idexp("y"), num(20)),
                                                        assign(idexp("x"), idexp("y"), idexp("y"), idexp("x"))
                                                )
                                        )
                                ),
                                Collections.emptyList(),
                                process(
                                        pcalVarDecl("MyProcess", false, false, num(32)),
                                        PlusCalFairness.WEAK_FAIR,
                                        Collections.emptyList(),
                                        labeled(label("l1"), assign(idexp("n"), num(2))),
                                        labeled(
                                                label("l2"),
                                                whileS(
                                                        binop("<", idexp("x"), num(10)),
                                                        new ArrayList<PlusCalStatement>() {{
                                                            add(
                                                                    assign(idexp("n"), num(12))
                                                            );

                                                            add(
                                                                    ifS(
                                                                            binop("=", idexp("n"), num(20)),
                                                                            Collections.singletonList(assign(idexp("n"), num(100))),
                                                                            Collections.emptyList()
                                                                    )
                                                            );
                                                        }}
                                                ),
                                                assign(idexp("n"), num(32))
                                        ),
                                        labeled(
                                                label("l3"),
                                                ifS(
                                                        binop("=", idexp("n"), num(12)),
                                                        Collections.singletonList(assign(idexp("n"), num(0))),
                                                        Collections.emptyList()
                                                ),
                                                assign(idexp("n"), num(12))
                                        )
                                )
                        ),
                        new ArrayList<Issue>() {{
                            add(new MissingLabelIssue(assign(idexp("x"), num(11))));
                            add(new MissingLabelIssue(assign(idexp("y"), num(11))));
                            add(new MissingLabelIssue(assign(idexp("x"), idexp("y"), idexp("y"), idexp("x"))));
                            add(new MissingLabelIssue(assign(idexp("n"), num(100))));
                            add(new MissingLabelIssue(assign(idexp("n"), num(12))));
                        }},
                },

                // --mpcal ReservedLabels {
                //     archetype MyArchetype() {
                //         Done: x := 10 (* reserved *)
                //         done: x := 10 (* no problem *)
                //     }
                //
                //     procedure MyProcedure() {
                //         p: either { p1: y := 20 } or { Error: skip }; (* reserved *)
                //     }
                // }
                {
                        mpcal(
                                "ReservedRules",
                                Collections.singletonList(
                                        archetype(
                                                "MyArchetype",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                new ArrayList<PlusCalStatement>() {{
                                                    add(
                                                            labeled(label("Done"), assign(idexp("x"), num(1)))
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
                                                "MyProcedure",
                                                Collections.emptyList(),
                                                Collections.emptyList(),
                                                labeled(
                                                        label("p"),
                                                        either(new ArrayList<List<PlusCalStatement>>() {{
                                                            add(Collections.singletonList(
                                                                    labeled(
                                                                            label("p1"),
                                                                            assign(idexp("y"), num(20))
                                                                    )
                                                            ));

                                                            add(Collections.singletonList(
                                                                    labeled(label("Error"), skip())
                                                            ));
                                                        }})
                                                )
                                        )
                                ),
                                Collections.emptyList()
                        ),
                        new ArrayList<Issue>() {{
                            add(new ReservedLabelNameIssue(labeled(label("Done"), assign(idexp("x"), num(1)))));
                            add(new ReservedLabelNameIssue(labeled(label("Error"), skip())));
                        }},
                },
        });
    }

    private ModularPlusCalBlock spec;
    private List<Issue> issues;

    public ModularPlusCalLabelingRulesTest(ModularPlusCalBlock spec, List<Issue> issues) {
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