package pgo.parser;

import pgo.model.mpcal.*;
import pgo.model.pcal.PlusCalVariableDeclaration;

import java.util.Collections;

import static pgo.parser.PlusCalParser.*;
import static pgo.parser.ParseTools.*;

public class ModularPlusCalParser {
	private ModularPlusCalParser() {}

	private static final Grammar<ModularPlusCalVariableDeclaration> MPCAL_VAR_DECL = emptySequence()
			.part(parseOneOf(
					parsePlusCalToken("ref").map(seq -> new Located<>(seq.getLocation(), true)),
					nop().map(seq -> new Located<>(seq.getLocation(), false))))
			.part(IDENTIFIER)
			.map(seq -> new ModularPlusCalVariableDeclaration(
					seq.getLocation(),
					seq.getValue().getFirst(),
					seq.getValue().getRest().getFirst().getValue()));

	private static final Grammar<ModularPlusCalArchetype> C_SYNTAX_ARCHETYPE = emptySequence()
			.drop(parsePlusCalToken("archetype"))
			.part(IDENTIFIER)
			.drop(parsePlusCalToken("("))
			.part(parseOneOf(
					parseListOf(MPCAL_VAR_DECL, parsePlusCalToken(",")),
					nop().map(seq ->
							new LocatedList<ModularPlusCalVariableDeclaration>(
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
					parseListOf(MPCAL_VAR_DECL, parsePlusCalToken(",")),
					nop().map(seq -> new LocatedList<ModularPlusCalVariableDeclaration>(
							seq.getLocation(),
							Collections.emptyList()))))
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


	// testing interface

	static ModularPlusCalUnit readUnit(LexicalContext ctx) throws ParseFailureException {
		return readOrExcept(ctx, parseOneOf(C_SYNTAX_ARCHETYPE, C_SYNTAX_INSTANCE));
	}
}
