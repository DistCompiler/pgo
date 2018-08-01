package pgo.model.tla;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import pgo.util.SourceLocation;

public class Builder {
	
	private Builder() {}
	
	public static PGoTLAFunction function(List<PGoTLAQuantifierBound> args, PGoTLAExpression body) {
		return new PGoTLAFunction(SourceLocation.unknown(), args, body);
	}
	
	public static List<PGoTLAQuantifierBound> bounds(PGoTLAQuantifierBound... bounds){
		return Arrays.asList(bounds);
	}
	
	public static List<PGoTLAIdentifier> ids(PGoTLAIdentifier... ids){
		return Arrays.asList(ids);
	}
	
	public static PGoTLAQuantifierBound qbIds(List<PGoTLAIdentifier> ids, PGoTLAExpression set) {
		return new PGoTLAQuantifierBound(SourceLocation.unknown(), PGoTLAQuantifierBound.Type.IDS, ids, set);
	}
	
	public static PGoTLAQuantifierBound qbTuple(List<PGoTLAIdentifier> ids, PGoTLAExpression set) {
		return new PGoTLAQuantifierBound(SourceLocation.unknown(), PGoTLAQuantifierBound.Type.TUPLE, ids, set);
	}
	
	public static PGoTLAIdentifier id(String name) {
		return new PGoTLAIdentifier(SourceLocation.unknown(), name);
	}
	
	public static PGoTLAGeneralIdentifierPart idpart(PGoTLAIdentifier id, PGoTLAExpression... args) {
		return new PGoTLAGeneralIdentifierPart(SourceLocation.unknown(), id, Arrays.asList(args));
	}
	
	public static PGoTLAGeneralIdentifierPart idpart(String id, PGoTLAExpression... args) {
		return idpart(id(id), args);
	}
	
	public static List<PGoTLAGeneralIdentifierPart> prefix(PGoTLAGeneralIdentifierPart... parts){
		return Arrays.asList(parts);
	}
	
	// expressions
	
	public static PGoTLAGeneralIdentifier idexp(List<PGoTLAGeneralIdentifierPart> prefix, PGoTLAIdentifier name) {
		return new PGoTLAGeneralIdentifier(SourceLocation.unknown(), name, prefix);
	}
	
	public static PGoTLAGeneralIdentifier idexp(List<PGoTLAGeneralIdentifierPart> prefix, String name) {
		return idexp(prefix, id(name));
	}
	
	public static PGoTLAGeneralIdentifier idexp(String name) {
		return idexp(prefix(), id(name));
	}
	
	public static PGoTLAString str(String contents) {
		return new PGoTLAString(SourceLocation.unknown(), contents);
	}
	
	public static PGoTLANumber num(int value) {
		return new PGoTLANumber(SourceLocation.unknown(), Integer.toString(value));
	}

	public static PGoTLASetConstructor set(PGoTLAExpression... members) {
		return new PGoTLASetConstructor(SourceLocation.unknown(), Arrays.asList(members));
	}
	
	public static PGoTLAOperatorCall opcall(List<PGoTLAGeneralIdentifierPart> prefix, PGoTLAIdentifier name, PGoTLAExpression... args) {
		return new PGoTLAOperatorCall(SourceLocation.unknown(), name, prefix, Arrays.asList(args));
	}
	
	public static PGoTLAOperatorCall opcall(String name, PGoTLAExpression... args) {
		return opcall(prefix(), id(name), args);
	}
	
	public static PGoTLAFunctionCall fncall(PGoTLAExpression fn, PGoTLAExpression... args) {
		return new PGoTLAFunctionCall(SourceLocation.unknown(), fn, Arrays.asList(args));
	}
	
	public static PGoTLASetRefinement setRefinement(String id, PGoTLAExpression set, PGoTLAExpression condition) {
		return new PGoTLASetRefinement(SourceLocation.unknown(), PGoTLAIdentifierOrTuple.Identifier(id(id)), set, condition);
	}
	
	public static PGoTLAFunctionSet functionSet(PGoTLAExpression from, PGoTLAExpression to) {
		return new PGoTLAFunctionSet(SourceLocation.unknown(), from, to);
	}
	
	public static PGoTLABinOp conjunct(PGoTLAExpression lhs, PGoTLAExpression rhs) {
		return new PGoTLABinOp(SourceLocation.unknown(), new PGoTLASymbol(SourceLocation.unknown(), "/\\"), prefix(), lhs, rhs);
	}
	
	public static PGoTLACaseArm arm(PGoTLAExpression cond, PGoTLAExpression result) {
		return new PGoTLACaseArm(SourceLocation.unknown(), cond, result);
	}
	
	public static List<PGoTLACaseArm> arms(PGoTLACaseArm... arms){
		return Arrays.asList(arms);
	}
	
	public static PGoTLACase caseexp(List<PGoTLACaseArm> arms, PGoTLAExpression other) {
		return new PGoTLACase(SourceLocation.unknown(), arms, other);
	}
	
	public static PGoTLASubstitutionKey key(PGoTLAExpression... indices) {
		return new PGoTLASubstitutionKey(SourceLocation.unknown(), Arrays.asList(indices));
	}
	
	public static List<PGoTLASubstitutionKey> keys(PGoTLASubstitutionKey... keys){
		return Arrays.asList(keys);
	}
	
	public static List<PGoTLASubstitutionKey> keys(PGoTLAExpression... keys){
		List<PGoTLASubstitutionKey> result = new ArrayList<>();
		for(PGoTLAExpression key : keys) {
			result.add(key(key));
		}
		return result;
	}
	
	public static PGoTLAFunctionSubstitutionPair sub(List<PGoTLASubstitutionKey> keys, PGoTLAExpression value) {
		return new PGoTLAFunctionSubstitutionPair(SourceLocation.unknown(), keys, value);
	}
	
	public static PGoTLAFunctionSubstitution except(PGoTLAExpression f, PGoTLAFunctionSubstitutionPair... subs) {
		return new PGoTLAFunctionSubstitution(SourceLocation.unknown(), f, Arrays.asList(subs));
	}
	
	public static PGoTLAUnary unary(List<PGoTLAGeneralIdentifierPart> prefix, String op, PGoTLAExpression arg) {
		return new PGoTLAUnary(SourceLocation.unknown(), new PGoTLASymbol(SourceLocation.unknown(), op), prefix, arg);
	}
	
	public static PGoTLAUnary unary(String op, PGoTLAExpression arg) {
		return unary(prefix(), op, arg);
	}
	
	public static PGoTLAQuantifiedUniversal universal(List<PGoTLAQuantifierBound> bounds, PGoTLAExpression expr) {
		return new PGoTLAQuantifiedUniversal(SourceLocation.unknown(), bounds, expr);
	}

	public static PGoTLAQuantifiedExistential existential(List<PGoTLAQuantifierBound> bounds, PGoTLAExpression expr) {
		return new PGoTLAQuantifiedExistential(SourceLocation.unknown(), bounds, expr);
	}

	public static PGoTLAModule module(String name, List<PGoTLAIdentifier> exts, List<PGoTLAUnit> preTranslationUnits, List<PGoTLAUnit> translatedUnits, List<PGoTLAUnit> postTranslationUnits) {
		return new PGoTLAModule(SourceLocation.unknown(), id(name), exts, preTranslationUnits, translatedUnits, postTranslationUnits);
	}
	
	public static List<PGoTLAOpDecl> opdecls(PGoTLAOpDecl... opdecls){
		return Arrays.asList(opdecls);
	}
	
	public static PGoTLAOpDecl opdecl(PGoTLAIdentifier name) {
		return PGoTLAOpDecl.Id(SourceLocation.unknown(), name);
	}
	
	public static PGoTLAOpDecl opdeclPrefix(PGoTLAIdentifier name) {
		return PGoTLAOpDecl.Prefix(SourceLocation.unknown(), name);
	}
	
	public static PGoTLAOpDecl opdeclPostfix(PGoTLAIdentifier name) {
		return PGoTLAOpDecl.Postfix(SourceLocation.unknown(), name);
	}
	
	public static PGoTLAOpDecl opdeclInfix(PGoTLAIdentifier name) {
		return PGoTLAOpDecl.Infix(SourceLocation.unknown(), name);
	}
	
	public static PGoTLAOpDecl opdeclNamed(PGoTLAIdentifier name, int arity) {
		return PGoTLAOpDecl.Named(SourceLocation.unknown(), name, arity);
	}
	
	public static PGoTLAOperatorDefinition opdef(boolean isLocal, PGoTLAIdentifier id, List<PGoTLAOpDecl> args, PGoTLAExpression body) {
		return new PGoTLAOperatorDefinition(SourceLocation.unknown(), id, args, body, isLocal);
	}
	
	public static PGoTLABinOp binop(String op, PGoTLAExpression lhs, PGoTLAExpression rhs) {
		return new PGoTLABinOp(SourceLocation.unknown(), new PGoTLASymbol(SourceLocation.unknown(), op), Collections.emptyList(), lhs, rhs);
	}
	
	public static PGoTLATuple tuple(PGoTLAExpression... expressions) {
		return new PGoTLATuple(SourceLocation.unknown(), Arrays.asList(expressions));
	}

	public static PGoTLAIf ifexp(PGoTLAExpression cond, PGoTLAExpression tval, PGoTLAExpression fval) {
		return new PGoTLAIf(SourceLocation.unknown(), cond, tval, fval);
	}

	public static PGoTLABool bool(Boolean value) {
		return new PGoTLABool(SourceLocation.unknown(), value);
	}

}
