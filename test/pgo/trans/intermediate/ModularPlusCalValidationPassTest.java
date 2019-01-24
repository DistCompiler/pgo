package pgo.trans.intermediate;

import static org.junit.Assert.*;

import java.util.*;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import pgo.errors.Issue;
import pgo.errors.TopLevelIssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.*;
import pgo.trans.passes.validation.*;

import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.mpcal.ModularPlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;

@RunWith(Parameterized.class)
public class ModularPlusCalValidationPassTest {

	@Parameters
	public static List<Object[]> data() {
		return Arrays.asList(new Object[][] {
				// --mpcal NoIssues {
				//	 archetype MyArchetype(ref x) {
				//		 l1: print(1 + 1);
				//		 l2: either { x := 10 } or { x := 20 };
				//	 }
				//
				//	 procedure MyProcedure(y) {
				//		 l2: print(3 - 3);
				//			 if (TRUE) {
				//				 y := 20;
				//			 } else {
				//				 y := 10;
				//			 }
				//	 }
				//
				//	 process (MyProcess = 32) {
				//		 l3: print(2 * 2);
				//	 }
				// }
				{
						mpcal(
								"NoIssues",
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										archetype(
												"MyArchetype",
												Collections.singletonList(pcalVarDecl(
														"x", true, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Collections.emptyList(),
												Arrays.asList(
														labeled(
																label("l1"),
																printS(binop("+", num(1), num(1)))
														),

														labeled(
																label("l2"),
																either (
																		Arrays.asList(
																				Collections.singletonList(
																						assign(idexp("x"), num(10))
																				),
																				Collections.singletonList(
																						assign(idexp("x"), num(20))
																				)
																		)
																)
														)
												)
										)
								),
								Collections.emptyList(),
								Collections.singletonList(
										procedure(
												"MyProcedure",
												Collections.singletonList(pcalVarDecl(
														"y", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
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
						Collections.emptyList()
				},

				// --mpcal ArchetypeNoFirstLabel {
				//	 archetype MyArchetype() {
				//		 print(1 + 1);
				//	 }
				// }
				{
						mpcal(
								"ArchetypeNoFirstLabel",
								Collections.emptyList(),
								Collections.emptyList(),
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
								Collections.emptyList()
						),
						Collections.singletonList(
								new MissingLabelIssue(printS(binop("+", num(1), num(1))))
						),
				},

				// --mpcal ProcedureNoFirstLabel {
				//	 procedure MyProcess() {
				//		 print(1 + 1);
				//	 }
				// }
				{
						mpcal(
								"ProcedureNoFirstLabel",
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
								Collections.emptyList(),
								Collections.emptyList()
						),
						Collections.singletonList(
								new MissingLabelIssue(printS(binop("+", num(1), num(1))))
						),
				},

				// --mpcal ProcessNoFirstLabel {
				//	 process MyProcess() {
				//		 print(1 + 1);
				//	 }
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
				//	 archetype ValidArchetype() {
				//		 l1: print(1 + 1);
				//	 }
				//
				//	 archetype InvalidArchetype() {
				//		 print("invalid archetype!");
				//	 }
				//
				//	 procedure ValidProcedure() {
				//		 l2: print(3 - 3);
				//	 }
				//
				//	 procedure InvalidProcedure() {
				//		 print("invalid procedure!");
				//	 }
				//
				//	 process (ValidProcess = 32) {
				//		 l3: print(2 * 2);
				//	 }
				//
				//	 process (InvalidProcess = 64) {
				//		 print("invalid process!");
				//	 }
				// }
				{
						mpcal(
								"MoreThanOneIssue",
								Collections.emptyList(),
								Collections.emptyList(),
								Arrays.asList(
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
										),
										archetype(
												"InvalidArchetype",
												Collections.emptyList(),
												Collections.emptyList(),
												Collections.singletonList(
														printS(str("invalid archetype!"))
												)
										)
								),
								Collections.emptyList(),
								Arrays.asList(
										procedure(
												"ValidProcedure",
												Collections.emptyList(),
												Collections.emptyList(),
												labeled(
														label("l2"),
														printS(binop("-", num(3), num(3)))
												)
										),
										procedure(
												"InvalidProcedure",
												Collections.emptyList(),
												Collections.emptyList(),
												printS(str("invalid procedure!"))
										)
								),
								Collections.emptyList(),
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

						Arrays.asList(
								new MissingLabelIssue(printS(str("invalid archetype!"))),
								new MissingLabelIssue(printS(str("invalid procedure!"))),
								new MissingLabelIssue(printS(str("invalid process!")))
						)
				},

				// --mpcal WhileLabels {
				//	 archetype IncorrectArchetype() {
				//		 l1: print "first label";
				//		 while (TRUE) { print "hello" }; (* missing label here *)
				//	 }
				//
				//	 procedure CorrectProcedure() {
				//		 l2: print "procedure";
				//		 l3: while (FALSE) { print(3 - 3) }; (* all good *)
				//	 }
				//
				//	 process (IncorrectProcess = 32) {
				//		 while (10 < 20) { print(2 * 2) }; (* missing label (first statement) *)
				//	 }
				// }
				{
						mpcal(
								"WhileLabels",
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										archetype(
												"IncorrectArchetype",
												Collections.emptyList(),
												Collections.emptyList(),
												Arrays.asList(
														labeled(label("l1"), printS(str("first label"))),
														whileS(bool(true), Collections.singletonList(
																printS(str("hello"))
														))
												)
										)
								),
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
						Arrays.asList(
								new MissingLabelIssue(
										whileS(bool(true), Collections.singletonList(
												printS(str("hello"))
										))
								),
								new MissingLabelIssue(
										whileS(binop("<", num(10), num(20)), Collections.singletonList(
												printS(binop("*", num(2), num(2))))
										)
								)
						)
				},

				// --mpcal CallLabelingRules {
				//	 archetype MyArchetype() {
				//		 l1: print "first label";
				//		 call MyProcedure();
				//		 call MyProcedure(); (* missing label *)
				//	 }
				//
				//	 procedure MyProcedure() {
				//		 l2: print "procedure";
				//		 call SomeProcedure();
				//		 return; (* no label required *)
				//	 }
				//
				//	 process (MyProcess = 32) {
				//		 l3: print "process";
				//		 call MyProcedure();
				//		 goto l3; (* no label required *)
				//		 l4: print "next label";
				//		 call MyProcedure();
				//		 x := 10; (* missing label *)
				//	 }
				// }
				{
						mpcal(
								"CallLabelingRules",
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										archetype(
												"MyArchetype",
												Collections.emptyList(),
												Collections.emptyList(),
												Arrays.asList(
														labeled(label("l1"), printS(str("first label"))),
														call("MyProcedure"),
														call("MyProcedure")
												)
										)
								),
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

						Arrays.asList(
								new MissingLabelIssue(call("MyProcedure")),
								new MissingLabelIssue(assign(idexp("x"), num(10)))
						)
				},

				// --mpcal ReturnGotoLabelingRules {
				//	 archetype MyArchetype() {
				//		 l1: print "first label";
				//		 goto l1;
				//		 print "needs label"; (* missing label *)
				//	 }
				//
				//	 procedure MyProcedure() {
				//		 l2: print "procedure";
				//		 return;
				//		 goto l2; (* missing label *)
				//	 }
				//
				//	 process (MyProcess = 32) {
				//		 l3: print "process";
				//		 goto l3;
				//		 x := 10; (* missing label *)
				//	 }
				// }
				{
						mpcal(
								"ReturnGotoLabelingRules",
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										archetype(
												"MyArchetype",
												Collections.emptyList(),
												Collections.emptyList(),
												Arrays.asList(
														labeled(label("l1"), printS(str("first label"))),
														gotoS("l1"),
														printS(str("needs label"))
												)
										)
								),
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

						Arrays.asList(
								new MissingLabelIssue(printS(str("needs label"))),
								new MissingLabelIssue(gotoS("l2")),
								new MissingLabelIssue(assign(idexp("x"), num(10)))
						)
				},

				// --mpcal IfEitherLabelingRules {
				//	 archetype MyArchetype() {
				//		 l1: print "first label";
				//		 if (TRUE) {
				//			 print "true";
				//		 } else if (TRUE) {
				//			 call MyProcedure();
				//		 }
				//
				//		 print "needs label"; (* missing label *)
				//	 }
				//
				//	 procedure MyProcedure() {
				//		 l2: print "procedure";
				//		 either { v := 10 } or { return };
				//		 goto l2; (* missing label *)
				//	 }
				//
				//	 process (MyProcess = 32) {
				//		 l3: print "process";
				//		 either { x := 0 } or { goto l3 };
				//		 l4: print "all good";
				//
				//		 either { goto l4 } or { skip };
				//		 x := 50; (* missing label *)
				//
				//		 l5: if (TRUE) {
				//				 l6: print "label";
				//			 }
				//		 y := 20; (* missing label *)
				//	 }
				// }
				{
						mpcal(
								"IfEitherLabelingRules",
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										archetype(
												"MyArchetype",
												Collections.emptyList(),
												Collections.emptyList(),
												Arrays.asList(
														labeled(label("l1"),
																printS(str("first label")),
																ifS(bool(true), Collections.singletonList(
																		printS(str("true"))
																), Collections.singletonList(
																		ifS(bool(true), Collections.singletonList(
																				call("MyProcedure")
																		), Collections.emptyList())
																))
														),
														printS(str("needs label"))
												)
										)
								),
								Collections.emptyList(),
								Collections.singletonList(
										procedure(
												"MyProcedure",
												Collections.emptyList(),
												Collections.emptyList(),
												labeled(label("l2"),
														printS(str("procedure")),
														either(Arrays.asList(
																Collections.singletonList(assign(idexp("v"), num(10))),
																Collections.singletonList(returnS())
														)),
														gotoS("l2"))
										)
								),
								Collections.emptyList(),
								Collections.emptyList(),
								process(
										pcalVarDecl("MyProcess", false, false, num(32)),
										PlusCalFairness.WEAK_FAIR,
										Collections.emptyList(),
										labeled(label("l3"), printS(str("process"))),
										either(Arrays.asList(
												Collections.singletonList(assign(idexp("x"), num(0))),
												Collections.singletonList(gotoS("l3"))
										)),
										labeled(label("l4"), printS(str("all good"))),
										either(Arrays.asList(
												Collections.singletonList(gotoS("l4")),
												Collections.singletonList(skip())
										)),
										assign(idexp("x"), num(50)),
										labeled(label("l5"), ifS(bool(true), Collections.singletonList(
												labeled(label("l6"), printS(str("label")))
										), Collections.emptyList())),
										assign(idexp("y"), num(20))
								)
						),

						Arrays.asList(
								new MissingLabelIssue(printS(str("needs label"))),
								new MissingLabelIssue(gotoS("l2")),
								new MissingLabelIssue(assign(idexp("x"), num(50))),
								new MissingLabelIssue(assign(idexp("y"), num(20)))
						)
				},

				// --mpcal MacroRules {
				//	 macro ValidMacro() {
				//		 print(1 + 1);
				//		 x := 10;
				//	 }
				//
				//	 macro InvalidMacro() {
				//		 either { skip } or { l1: y := 10 }; (* invalid *)
				//		 l2: y := 20; (* invalid *)
				//	 }
				// }
				{
						mpcal(
								"MacroRules",
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList(),
								Arrays.asList(
										macro(
												"ValidMacro",
												Collections.emptyList(),
												printS(binop("+", num(1), num(1))),
												assign(idexp("x"), num(10))
										),
										macro(
												"InvalidMacro",
												Collections.emptyList(),
												either(Arrays.asList(
														Collections.singletonList(skip()),
														Collections.singletonList(labeled(label("l1"), assign(idexp("y"), num(10))))
												)),
												labeled(label("l2"), assign(idexp("y"), num(20)))
										)
								),
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.emptyList()
						),

						Arrays.asList(
								new LabelNotAllowedIssue(labeled(label("l1"), assign(idexp("y"), num(10)))),
								new LabelNotAllowedIssue(labeled(label("l2"), assign(idexp("y"), num(20))))
						)
				},

				// --mpcal WithRules {
				//	 macro MacroWith() {
				//		 print(1 + 1);
				//		 with (x = 10) {
				//			 print x;
				//			 m1: x := 20; (* invalid *)
				//		 }
				//		 m2: y := 20; (* invalid *)
				//	 }
				//
				//	 procedure ProcedureWith() {
				//		 l1: with (x = 10) {
				//				 l2: print x; (* invalid *)
				//			 }
				//	 }
				// }
				{
						mpcal(
								"WithRules",
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
								Collections.emptyList(),
								Collections.emptyList()
						),

						Arrays.asList(
								new LabelNotAllowedIssue(labeled(label("m1"), assign(idexp("x"), num(20)))),
								new LabelNotAllowedIssue(labeled(label("m2"), assign(idexp("y"), num(20)))),
								new LabelNotAllowedIssue(labeled(label("l2"), printS(idexp("x"))))
						)
				},

				// --mpcal AssignmentRules {
				//	 archetype MyArchetype(ref x) {
				//		 a1: x := 10;
				//		 x := 11; (* missing label *)
				//	 }
				//
				//	 procedure MyProcedure(x, y) {
				//		 p: either { y := 10 } or { skip };
				//			y := 11; (* missing label *)
				//		 p2: y := 20;
				//			 x := y || y := x; (* swap x and y: invalid *)
				//	 }
				//
				//	 process (MyProcess = 23)
				//   variables n;
				//   {
				//		 l1: n := 2;
				//		 l2: while (n < 10) {
				//			 n := 12;
				//			 if (n := 20) {
				//				 n := 100; (* missing label *)
				//			 }
				//		 };
				//		 n := 32; (* label not missing *)
				//
				//		 l3: if (n = 32) {
				//			 n := 0;
				//		 };
				//		 n := 12; (* missing label *)
				//	 }
				// }
				{
						mpcal(
								"AssignmentRules",
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										archetype(
												"MyArchetype",
												Collections.singletonList(pcalVarDecl(
														"x", true, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Collections.emptyList(),
												Collections.singletonList(
														labeled(
																label("a1"),
																assign(idexp("x"), num(10)),
																assign(idexp("x"), num(11))
														)
												)
										)
								),
								Collections.emptyList(),
								Collections.singletonList(
										procedure(
												"MyProcedure",
												Arrays.asList(
														pcalVarDecl("x", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
														pcalVarDecl("y", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Collections.emptyList(),
												labeled(
														label("p"),
														either(Arrays.asList(
																Collections.singletonList(assign(idexp("y"), num(10))),
																Collections.singletonList(skip())
														)),
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
								Collections.emptyList(),
								process(
										pcalVarDecl("MyProcess", false, false, num(32)),
										PlusCalFairness.WEAK_FAIR,
										Collections.singletonList(pcalVarDecl(
												"n", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
										labeled(label("l1"), assign(idexp("n"), num(2))),
										labeled(
												label("l2"),
												whileS(
														binop("<", idexp("x"), num(10)),
														Arrays.asList(
																assign(idexp("n"), num(12)),
																ifS(
																		binop("=", idexp("n"), num(20)),
																		Collections.singletonList(assign(idexp("n"), num(100))),
																		Collections.emptyList()
																)
														)
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
						Arrays.asList(
								new MissingLabelIssue(assign(idexp("x"), num(11))),
								new MissingLabelIssue(assign(idexp("y"), num(11))),
								new MissingLabelIssue(assign(idexp("x"), idexp("y"), idexp("y"), idexp("x"))),
								new MissingLabelIssue(assign(idexp("n"), num(100))),
								new MissingLabelIssue(assign(idexp("n"), num(12)))
						)
				},

				// --mpcal ReservedLabels {
				//	 archetype MyArchetype(ref x) {
				//		 Done: x := 10 (* reserved *)
				//		 done: x := 10 (* no problem *)
				//	 }
				//
				//	 procedure MyProcedure(y) {
				//		 p: either { p1: y := 20 } or { Error: skip }; (* reserved *)
				//	 }
				// }
				{
						mpcal(
								"ReservedRules",
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(
										archetype(
												"MyArchetype",
												Arrays.asList(pcalVarDecl(
														"x", true, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Collections.emptyList(),
												Collections.singletonList(
														labeled(label("Done"), assign(idexp("x"), num(1)))
												)
										)
								),
								Collections.emptyList(),
								Collections.singletonList(
										procedure(
												"MyProcedure",
												Collections.singletonList(pcalVarDecl(
														"y", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
												Collections.emptyList(),
												labeled(
														label("p"),
														either(Arrays.asList(
																Collections.singletonList(
																		labeled(
																				label("p1"),
																				assign(idexp("y"), num(20))
																		)
																),
																Collections.singletonList(
																		labeled(label("Error"), skip())
																)
														))
												)
										)
								),
								Collections.emptyList(),
								Collections.emptyList()
						),
						Arrays.asList(
								new ReservedLabelNameIssue(labeled(label("Done"), assign(idexp("x"), num(1)))),
								new ReservedLabelNameIssue(labeled(label("Error"), skip()))
						)
				},

				// --mpcal MappingWithLabels {
				//	 mapping macro ContainsLabels {
				//		 read {
				//           r: yield $variable
				//       }
				//       write {
				//           if ($variable > 10) {
				//               yield $value;
				//           }
				//       }
				//	 }
				// }
				{
					mpcal(
							"MappingWithLabels",
							Collections.emptyList(),
							Collections.singletonList(
									mappingMacro(
											"ContainsLabels",
											Collections.singletonList(
													labeled(
															label("l"),
															yield(DOLLAR_VARIABLE)
													)
											),
											Collections.singletonList(
													labeled(
															label("w"),
															yield(DOLLAR_VALUE)
													)
											)
									)
							),
							Collections.emptyList(),
							Collections.emptyList(),
							Collections.emptyList(),
							Collections.emptyList(),
							Collections.emptyList()
					),

					Arrays.asList(
							new StatementNotAllowedIssue(labeled(label("l"), yield(DOLLAR_VARIABLE))),
							new StatementNotAllowedIssue(labeled(label("w"), yield(DOLLAR_VALUE)))
					)
				},

				// --mpcal MappingMacroWithCallGoto {
				//	 mapping macro InvalidStatements {
				//		 read {
				//           await Len($variable) = 0;
				//           if (TRUE) {
				//               call YesProcedure();
				//           }
				//           call NoProcedure();
				//           yield 0;
				//       }
				//       write {
				//           either { yield $value }
				//           or     { goto l1 }
				//       }
				//	 }
				// }
				{
					mpcal(
							"MappingMacroWithcallGoto",
							Collections.emptyList(),
							Collections.singletonList(
									mappingMacro(
											"InvalidStatements",
											Arrays.asList(
													await(binop("=", opcall("Len", DOLLAR_VARIABLE), num(0))),
													ifS(
															bool(true),
															Collections.singletonList(call("YesProcedure")),
															Collections.emptyList()
													),
													call("NoProcedure"),
													yield(num(0))
											),
											Collections.singletonList(
													either(Arrays.asList(
															Collections.singletonList(yield(DOLLAR_VALUE)),
															Collections.singletonList(gotoS("l1")))
													)
											)
									)
							),
							Collections.emptyList(),
							Collections.emptyList(),
							Collections.emptyList(),
							Collections.emptyList(),
							Collections.emptyList()
					),

					Arrays.asList(
							new StatementNotAllowedIssue(call("YesProcedure")),
							new StatementNotAllowedIssue(call("NoProcedure")),
							new StatementNotAllowedIssue(gotoS("l1"))
					)
				}
		});
	}

	private ModularPlusCalBlock spec;
	private List<Issue> issues;

	public ModularPlusCalValidationPassTest(ModularPlusCalBlock spec, List<Issue> issues) {
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