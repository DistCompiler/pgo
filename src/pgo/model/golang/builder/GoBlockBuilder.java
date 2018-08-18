package pgo.model.golang.builder;

import pgo.InternalCompilerError;
import pgo.model.golang.*;
import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;
import pgo.scope.UID;

import java.io.Closeable;
import java.util.*;

public class GoBlockBuilder extends GoASTBuilder implements Closeable {

	private GoASTBuilder builder;
	private NameCleaner nameCleaner;
	private Map<UID, GoVariableName> nameMap;
	private List<GoStatement> statements;

	public interface OnSuccess {
		void action(GoBlock block);
	}

	private OnSuccess onSuccess;
	private NameCleaner labelScope;

	public GoBlockBuilder(GoASTBuilder builder, NameCleaner nameCleaner, Map<UID, GoVariableName> nameMap, NameCleaner labelScope) {
		this.builder = builder;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		this.statements = new ArrayList<>();
		this.onSuccess = builder::addBlock;
	}

	public GoBlockBuilder(GoASTBuilder builder, NameCleaner nameCleaner, Map<UID, GoVariableName> nameMap, NameCleaner labelScope, OnSuccess onSuccess) {
		this.builder = builder;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		this.statements = new ArrayList<>();
		this.onSuccess = onSuccess;
	}

	public GoBlock getBlock() {
		return new GoBlock(statements);
	}

	public GoLabelName newLabel(String nameHint) {
		String name = labelScope.cleanName(nameHint);
		return new GoLabelName(name);
	}

	public void label(GoLabelName label) {
		addStatement(new GoLabel(label.getName()));
	}

	public void labelIsUnique(String name) {
		labelScope.requireCleanName(name);
		statements.add(new GoLabel(name));
	}

	public void assign(GoExpression name, GoExpression value) {
		assign(Collections.singletonList(name), Collections.singletonList(value));
	}

	public void assign(List<GoExpression> names, GoExpression value) {
		assign(names, Collections.singletonList(value));
	}

	public void assign(List<GoExpression> names, List<GoExpression> values) {
		addStatement(new GoAssignmentStatement(names, false, values));
	}

	public GoASTBuilder getParent() {
		return builder;
	}

	public GoIfBuilder ifStmt(GoExpression condition) {
		return new GoIfBuilder(this, nameCleaner.child(), nameMap, labelScope, condition);
	}

	public void print(GoExpression value) {
		addImport("fmt");
		addStatement(
				new GoExpressionStatement(
						new GoCall(
								new GoSelectorExpression(
										new GoVariableName("fmt"), "Printf"),
								Arrays.asList(new GoStringLiteral("%v\\n"), value))));
	}

	public GoBlockBuilder forLoop(GoExpression condition) {
		return new GoBlockBuilder(
				this, nameCleaner.child(), nameMap, labelScope,
				block -> addStatement(new GoFor(null, condition, null, block)));
	}

	public GoForStatementClauseBuilder forLoopWithClauses() {
		return new GoForStatementClauseBuilder(this, nameCleaner.child(), nameMap, labelScope);
	}

	public GoForRangeBuilder forRange(GoExpression rangeExp) {
		return new GoForRangeBuilder(this, nameCleaner.child(), nameMap, labelScope, rangeExp);
	}

	public GoSwitchBuilder switchStmt(GoExpression switchExp) {
		return new GoSwitchBuilder(this, nameCleaner.child(), nameMap, labelScope, switchExp);
	}

	private List<GoVariableName> getFreshNames(List<String> nameHints) {
		List<GoVariableName> ret = new ArrayList<>();
		for (String hint : nameHints) {
			GoVariableName variableName = getFreshName(hint);
			ret.add(variableName);
		}
		return ret;
	}

	public List<GoVariableName> varDecl(List<String> nameHints, GoExpression value) {
		List<GoVariableName> ret = getFreshNames(nameHints);
		List<GoExpression> names = new ArrayList<>(ret);
		addStatement(new GoAssignmentStatement(names, true, Collections.singletonList(value)));
		return ret;
	}

	public GoVariableName varDecl(String nameHint, GoExpression value) {
		return varDecl(Collections.singletonList(nameHint), value).get(0);
	}

	public GoVariableName varDecl(String nameHint, GoType type) {
		GoVariableName ret = getFreshNames(Collections.singletonList(nameHint)).get(0);
		String name = ret.getName();
		addStatement(new GoVariableDeclarationStatement(new GoVariableDeclaration(name, type, null)));
		return ret;
	}

	public GoVariableName getFreshName(String nameHint) {
		String actualName = nameCleaner.cleanName(nameHint);
		return new GoVariableName(actualName);
	}

	public void goTo(GoLabelName name) {
		addStatement(new GoTo(name));
	}

	public void addPanic(GoExpression e) {
		addStatement(new GoExpressionStatement(new GoCall(new GoVariableName("panic"), Collections.singletonList(e))));
	}

	public void addStatement(GoExpression expression) {
		addStatement(new GoExpressionStatement(expression));
	}

	@Override
	public void addStatement(GoStatement s) {
		statements.add(s);
	}

	@Override
	protected void addBlock(GoBlock block) {
		statements.add(block);
	}

	@Override
	protected void addFunction(GoFunctionDeclaration fn) {
		builder.addFunction(fn);
	}

	@Override
	public void close() {
		onSuccess.action(getBlock());
	}

	@Override
	public GoTypeName defineType(String nameHint, GoType type) {
		return builder.defineType(nameHint, type);
	}

	@Override
	public GoFunctionDeclarationBuilder defineFunction(UID uid, String nameHint) {
		return builder.defineFunction(uid, nameHint);
	}

	public GoAnonymousFunctionBuilder anonymousFunction() {
		return new GoAnonymousFunctionBuilder(this, nameCleaner, nameMap);
	}

	public void goStmt(GoExpression expression) {
		addStatement(new GoRoutineStatement(expression));
	}

	public void deferStmt(GoExpression expression) {
		addStatement(new GoDefer(expression));
	}

	public void returnStmt(GoExpression... values) {
		addStatement(new GoReturn(Arrays.asList(values)));
	}

	public void linkUID(UID uid, GoVariableName name) {
		nameMap.put(uid, name);
	}

	public GoVariableName findUID(UID uid) {
		if(!nameMap.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		return nameMap.get(uid);
	}

	@Override
	public void addImport(String name) {
		builder.addImport(name);
	}
}
