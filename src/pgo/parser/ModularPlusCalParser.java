package pgo.parser;

import pgo.model.mpcal.*;
import pgo.model.pcal.PlusCalMultiProcess;
import pgo.model.pcal.PlusCalSingleProcess;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAUnit;

import java.util.Collections;
import java.util.regex.Pattern;

import static pgo.parser.PlusCalParser.*;
import static pgo.parser.ParseTools.*;

public class ModularPlusCalParser {
	private ModularPlusCalParser() {}

	private static final Pattern FIND_MPCAL = Pattern.compile(".*?\\(\\*.*?(?=--mpcal)", Pattern.DOTALL);
	private static final Pattern AFTER_MPCAL = Pattern.compile(".*?\\*\\).*$", Pattern.DOTALL);

	private static final Grammar<PlusCalVariableDeclaration> MPCAL_VAR_DECL = emptySequence()
			.part(parseOneOf(
					parsePlusCalToken("ref").map(seq -> new Located<>(seq.getLocation(), true)),
					nop().map(seq -> new Located<>(seq.getLocation(), false))))
			.part(IDENTIFIER)
			.map(seq -> new PlusCalVariableDeclaration(
					seq.getLocation(),
					seq.getValue().getFirst(),
					seq.getValue().getRest().getFirst().getValue(),
					false,
					new PlusCalDefaultInitValue(seq.getLocation())));

	private static final Grammar<ModularPlusCalArchetype> C_SYNTAX_ARCHETYPE = emptySequence()
			.drop(parsePlusCalToken("archetype"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(MPCAL_VAR_DECL, parsePlusCalToken(",")),
					nop().map(seq ->
							new LocatedList<PlusCalVariableDeclaration>(
									seq.getLocation(),
									Collections.emptyList()))))
			.drop(parsePlusCalToken(")"))
			.part(parseOneOf(
					VAR_DECLS,
					nop().map(seq -> new LocatedList<PlusCalVariableDeclaration>(
							seq.getLocation(),
							Collections.emptyList()))))
			.part(C_SYNTAX_COMPOUND_STMT)
			.map(seq -> new ModularPlusCalArchetype(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<ModularPlusCalMapping> MAPPING = emptySequence()
			.drop(parsePlusCalToken("mapping"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("via"))
			.part(IDENTIFIER)
			.map(seq -> new ModularPlusCalMapping(
					seq.getLocation(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst().getValue()));

	private static final Grammar<ModularPlusCalInstance> C_SYNTAX_INSTANCE = emptySequence()
			.drop(parsePlusCalToken("process"))
			.drop(parsePlusCalToken("("))
			.part(VARIABLE_DECLARATION)
			.drop(parsePlusCalToken(")"))
			.drop(parsePlusCalToken("="))
			.drop(parsePlusCalToken("instance"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(MODULAR_PLUSCAL_PARAMETER, parsePlusCalToken(",")),
					nop().map(seq -> new LocatedList<TLAExpression>(seq.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken(")"))
			.part(parseOneOf(
					parseListOf(MAPPING, nop()),
					nop().map(seq ->
							new LocatedList<ModularPlusCalMapping>(seq.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken(";"))
			.map(seq -> new ModularPlusCalInstance(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getFirst().getValue(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<ModularPlusCalMappingMacro> C_SYNTAX_MAPPING_MACRO = emptySequence()
			.drop(parsePlusCalToken("mapping"))
			.drop(parsePlusCalToken("macro"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("{"))
			.drop(parsePlusCalToken("read"))
			.drop(parsePlusCalToken("{"))
			.part(parseListOf(C_SYNTAX_UNLABELED_STMT, parsePlusCalToken(";")))
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.drop(parsePlusCalToken("}"))
			.drop(parsePlusCalToken("write"))
			.drop(parsePlusCalToken("{"))
			.part(parseListOf(C_SYNTAX_UNLABELED_STMT, parsePlusCalToken(";")))
			.drop(parseOneOf(parsePlusCalToken(";"), nop()))
			.drop(parsePlusCalToken("}"))
			.drop(parsePlusCalToken("}"))
			.map(seq -> new ModularPlusCalMappingMacro(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<ModularPlusCalBlock> C_SYNTAX_MPCAL = emptySequence()
			.drop(parsePlusCalToken("--mpcal"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("{"))
			.part(parseOneOf(
					VAR_DECLS,
					nop().map(seq -> new LocatedList<PlusCalVariableDeclaration>(
							seq.getLocation(),
							Collections.emptyList()))))
			.part(parseOneOf(
					C_SYNTAX_DEFINITIONS,
					nop().map(seq -> new LocatedList<TLAUnit>(seq.getLocation(), Collections.emptyList()))))
			.part(parseOneOf(
					parseListOf(C_SYNTAX_MAPPING_MACRO, nop()),
					nop().map(seq -> new LocatedList<ModularPlusCalMappingMacro>(
							seq.getLocation(),
							Collections.emptyList()))))
			.part(parseOneOf(
					parseListOf(C_SYNTAX_ARCHETYPE, nop()),
					nop().map(seq -> new LocatedList<ModularPlusCalArchetype>(
							seq.getLocation(),
							Collections.emptyList()))))
			.part(repeat(C_SYNTAX_MACRO))
			.part(repeat(C_SYNTAX_PROCEDURE))
			.part(repeat(C_SYNTAX_INSTANCE))
			.part(parseOneOf(
					C_SYNTAX_COMPOUND_STMT.map(stmts -> new PlusCalSingleProcess(stmts.getLocation(), stmts)),
					repeatOneOrMore(C_SYNTAX_PROCESS).map(procs -> new PlusCalMultiProcess(procs.getLocation(), procs)),
					nop().map(seq -> new PlusCalMultiProcess(seq.getLocation(), Collections.emptyList()))))
			.drop(parsePlusCalToken("}"))
			.map(seq -> new ModularPlusCalBlock(
					seq.getLocation(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getRest().getFirst(),
					seq.getValue().getRest().getRest().getFirst(),
					seq.getValue().getRest().getFirst(),
					seq.getValue().getFirst()));

	private static final Grammar<ModularPlusCalBlock> MPCAL_BLOCK = emptySequence()
			.drop(matchPattern(FIND_MPCAL))
			.part(parseOneOf(C_SYNTAX_MPCAL))
			.drop(matchPattern(AFTER_MPCAL))
			.map(seq -> seq.getValue().getFirst());

	// public interface

	public static ModularPlusCalBlock readBlock(LexicalContext ctx) throws ParseFailureException {
		return readOrExcept(ctx, MPCAL_BLOCK);
	}

	// testing interface

	static ModularPlusCalUnit readUnit(LexicalContext ctx) throws ParseFailureException {
		return readOrExcept(ctx, parseOneOf(C_SYNTAX_ARCHETYPE, C_SYNTAX_INSTANCE, C_SYNTAX_MAPPING_MACRO));
	}
}
