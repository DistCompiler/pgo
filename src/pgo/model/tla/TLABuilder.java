package pgo.model.tla;

import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class TLABuilder {
	private TLABuilder() {}

	public static TLASpecialVariableVariable DOLLAR_VARIABLE = new TLASpecialVariableVariable(SourceLocation.unknown());
	public static TLASpecialVariableValue DOLLAR_VALUE = new TLASpecialVariableValue(SourceLocation.unknown());
	
	public static TLAFunction function(List<TLAQuantifierBound> args, TLAExpression body) {
		return new TLAFunction(SourceLocation.unknown(), args, body);
	}
	
	public static List<TLAQuantifierBound> bounds(TLAQuantifierBound... bounds){
		return Arrays.asList(bounds);
	}
	
	public static List<TLAIdentifier> ids(TLAIdentifier... ids){
		return Arrays.asList(ids);
	}
	
	public static TLAQuantifierBound qbIds(List<TLAIdentifier> ids, TLAExpression set) {
		return new TLAQuantifierBound(SourceLocation.unknown(), TLAQuantifierBound.Type.IDS, ids, set);
	}
	
	public static TLAQuantifierBound qbTuple(List<TLAIdentifier> ids, TLAExpression set) {
		return new TLAQuantifierBound(SourceLocation.unknown(), TLAQuantifierBound.Type.TUPLE, ids, set);
	}
	
	public static TLAIdentifier id(String name) {
		return new TLAIdentifier(SourceLocation.unknown(), name);
	}
	
	public static TLAGeneralIdentifierPart idpart(TLAIdentifier id, TLAExpression... args) {
		return new TLAGeneralIdentifierPart(SourceLocation.unknown(), id, Arrays.asList(args));
	}
	
	public static TLAGeneralIdentifierPart idpart(String id, TLAExpression... args) {
		return idpart(id(id), args);
	}
	
	public static List<TLAGeneralIdentifierPart> prefix(TLAGeneralIdentifierPart... parts){
		return Arrays.asList(parts);
	}
	
	// expressions
	
	public static TLAGeneralIdentifier idexp(List<TLAGeneralIdentifierPart> prefix, TLAIdentifier name) {
		return new TLAGeneralIdentifier(SourceLocation.unknown(), name, prefix);
	}
	
	public static TLAGeneralIdentifier idexp(List<TLAGeneralIdentifierPart> prefix, String name) {
		return idexp(prefix, id(name));
	}
	
	public static TLAGeneralIdentifier idexp(String name) {
		return idexp(prefix(), id(name));
	}
	
	public static TLAString str(String contents) {
		return new TLAString(SourceLocation.unknown(), contents);
	}
	
	public static TLANumber num(int value) {
		return new TLANumber(SourceLocation.unknown(), Integer.toString(value), TLANumber.Base.DECIMAL);
	}

	public static TLASetConstructor set(TLAExpression... members) {
		return new TLASetConstructor(SourceLocation.unknown(), Arrays.asList(members));
	}
	
	public static TLAOperatorCall opcall(List<TLAGeneralIdentifierPart> prefix, TLAIdentifier name, TLAExpression... args) {
		return new TLAOperatorCall(SourceLocation.unknown(), name, prefix, Arrays.asList(args));
	}
	
	public static TLAOperatorCall opcall(String name, TLAExpression... args) {
		return opcall(prefix(), id(name), args);
	}
	
	public static TLAFunctionCall fncall(TLAExpression fn, TLAExpression... args) {
		return new TLAFunctionCall(SourceLocation.unknown(), fn, Arrays.asList(args));
	}
	
	public static TLASetRefinement setRefinement(String id, TLAExpression set, TLAExpression condition) {
		return new TLASetRefinement(SourceLocation.unknown(), TLAIdentifierOrTuple.Identifier(id(id)), set, condition);
	}
	
	public static TLAFunctionSet functionSet(TLAExpression from, TLAExpression to) {
		return new TLAFunctionSet(SourceLocation.unknown(), from, to);
	}
	
	public static TLABinOp conjunct(TLAExpression lhs, TLAExpression rhs) {
		return new TLABinOp(SourceLocation.unknown(), new TLASymbol(SourceLocation.unknown(), "/\\"), prefix(), lhs, rhs);
	}
	
	public static TLACaseArm arm(TLAExpression cond, TLAExpression result) {
		return new TLACaseArm(SourceLocation.unknown(), cond, result);
	}
	
	public static List<TLACaseArm> arms(TLACaseArm... arms){
		return Arrays.asList(arms);
	}
	
	public static TLACase caseexp(List<TLACaseArm> arms, TLAExpression other) {
		return new TLACase(SourceLocation.unknown(), arms, other);
	}
	
	public static TLASubstitutionKey key(TLAExpression... indices) {
		return new TLASubstitutionKey(SourceLocation.unknown(), Arrays.asList(indices));
	}
	
	public static List<TLASubstitutionKey> keys(TLASubstitutionKey... keys){
		return Arrays.asList(keys);
	}
	
	public static List<TLASubstitutionKey> keys(TLAExpression... keys){
		List<TLASubstitutionKey> result = new ArrayList<>();
		for(TLAExpression key : keys) {
			result.add(key(key));
		}
		return result;
	}
	
	public static TLAFunctionSubstitutionPair sub(List<TLASubstitutionKey> keys, TLAExpression value) {
		return new TLAFunctionSubstitutionPair(SourceLocation.unknown(), keys, value);
	}
	
	public static TLAFunctionSubstitution except(TLAExpression f, TLAFunctionSubstitutionPair... subs) {
		return new TLAFunctionSubstitution(SourceLocation.unknown(), f, Arrays.asList(subs));
	}
	
	public static TLAUnary unary(List<TLAGeneralIdentifierPart> prefix, String op, TLAExpression arg) {
		return new TLAUnary(SourceLocation.unknown(), new TLASymbol(SourceLocation.unknown(), op), prefix, arg);
	}
	
	public static TLAUnary unary(String op, TLAExpression arg) {
		return unary(prefix(), op, arg);
	}
	
	public static TLAQuantifiedUniversal universal(List<TLAQuantifierBound> bounds, TLAExpression expr) {
		return new TLAQuantifiedUniversal(SourceLocation.unknown(), bounds, expr);
	}

	public static TLAQuantifiedExistential existential(List<TLAQuantifierBound> bounds, TLAExpression expr) {
		return new TLAQuantifiedExistential(SourceLocation.unknown(), bounds, expr);
	}

	public static TLAModule module(String name, List<TLAIdentifier> exts, List<TLAUnit> preTranslationUnits, List<TLAUnit> translatedUnits, List<TLAUnit> postTranslationUnits) {
		return new TLAModule(SourceLocation.unknown(), id(name), exts, preTranslationUnits, translatedUnits, postTranslationUnits);
	}
	
	public static List<TLAOpDecl> opdecls(TLAOpDecl... opdecls){
		return Arrays.asList(opdecls);
	}
	
	public static TLAOpDecl opdecl(TLAIdentifier name) {
		return TLAOpDecl.Id(SourceLocation.unknown(), name);
	}
	
	public static TLAOpDecl opdeclPrefix(TLAIdentifier name) {
		return TLAOpDecl.Prefix(SourceLocation.unknown(), name);
	}
	
	public static TLAOpDecl opdeclPostfix(TLAIdentifier name) {
		return TLAOpDecl.Postfix(SourceLocation.unknown(), name);
	}
	
	public static TLAOpDecl opdeclInfix(TLAIdentifier name) {
		return TLAOpDecl.Infix(SourceLocation.unknown(), name);
	}
	
	public static TLAOpDecl opdeclNamed(TLAIdentifier name, int arity) {
		return TLAOpDecl.Named(SourceLocation.unknown(), name, arity);
	}
	
	public static TLAOperatorDefinition opdef(boolean isLocal, TLAIdentifier id, List<TLAOpDecl> args, TLAExpression body) {
		return new TLAOperatorDefinition(SourceLocation.unknown(), id, args, body, isLocal);
	}
	
	public static TLABinOp binop(String op, TLAExpression lhs, TLAExpression rhs) {
		return new TLABinOp(SourceLocation.unknown(), new TLASymbol(SourceLocation.unknown(), op), Collections.emptyList(), lhs, rhs);
	}
	
	public static TLATuple tuple(TLAExpression... expressions) {
		return new TLATuple(SourceLocation.unknown(), Arrays.asList(expressions));
	}

	public static TLAIf ifexp(TLAExpression cond, TLAExpression tval, TLAExpression fval) {
		return new TLAIf(SourceLocation.unknown(), cond, tval, fval);
	}

	public static TLAFairness fairness(TLAFairness.Type type, TLAExpression vars, TLAExpression expression){
		return new TLAFairness(SourceLocation.unknown(), type, vars, expression);
	}

	public static TLABool bool(boolean val) {
		return new TLABool(SourceLocation.unknown(), val);
	}

	public static TLARef ref(String name) {
		return new TLARef(SourceLocation.unknown(), name);
	}
}
