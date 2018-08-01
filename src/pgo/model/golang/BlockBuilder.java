package pgo.model.golang;

import java.io.Closeable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import pgo.InternalCompilerError;
import pgo.scope.UID;

public class BlockBuilder extends ASTBuilder implements Closeable {

	private ASTBuilder builder;
	private NameCleaner nameCleaner;
	private Map<UID, VariableName> nameMap;
	private List<Statement> statements;

	public interface OnSuccess {
		void action(Block block);
	}

	private OnSuccess onSuccess;
	private NameCleaner labelScope;

	public BlockBuilder(ASTBuilder builder, NameCleaner nameCleaner, Map<UID, VariableName> nameMap, NameCleaner labelScope) {
		this.builder = builder;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		this.statements = new ArrayList<>();
		this.onSuccess = builder::addBlock;
	}

	public BlockBuilder(ASTBuilder builder, NameCleaner nameCleaner, Map<UID, VariableName> nameMap, NameCleaner labelScope, OnSuccess onSuccess) {
		this.builder = builder;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		this.statements = new ArrayList<>();
		this.onSuccess = onSuccess;
	}

	public Block getBlock() {
		return new Block(statements);
	}

	public LabelName newLabel(String nameHint) {
		String name = labelScope.cleanName(nameHint);
		return new LabelName(name);
	}

	public void label(LabelName label) {
		addStatement(new Label(label.getName()));
	}

	public void labelIsUnique(String name) {
		labelScope.requireCleanName(name);
		statements.add(new Label(name));
	}

	public void assign(Expression name, Expression value) {
		assign(Collections.singletonList(name), Collections.singletonList(value));
	}

	public void assign(List<Expression> names, Expression value) {
		assign(names, Collections.singletonList(value));
	}

	public void assign(List<Expression> names, List<Expression> values) {
		addStatement(new Assignment(names, false, values));
	}

	public ASTBuilder getParent() {
		return builder;
	}

	public IfBuilder ifStmt(Expression condition) {
		return new IfBuilder(this, nameCleaner.child(), nameMap, labelScope, condition);
	}

	public void print(Expression value) {
		addImport("fmt");
		addStatement(
				new ExpressionStatement(
						new Call(
								new Selector(
										new VariableName("fmt"), "Printf"),
								Arrays.asList(new StringLiteral("%v\\n"), value))));
	}

	public BlockBuilder forLoop(Expression condition) {
		return new BlockBuilder(
				this, nameCleaner.child(), nameMap, labelScope,
				block -> addStatement(new For(null, condition, null, block)));
	}

	public ForStatementClauseBuilder forLoopWithClauses() {
		return new ForStatementClauseBuilder(this, nameCleaner.child(), nameMap, labelScope);
	}

	public ForRangeBuilder forRange(Expression rangeExp) {
		return new ForRangeBuilder(this, nameCleaner.child(), nameMap, labelScope, rangeExp);
	}

	public SwitchBuilder switchStmt(Expression switchExp) {
		return new SwitchBuilder(this, nameCleaner.child(), nameMap, labelScope, switchExp);
	}

	private List<VariableName> getFreshNames(List<String> nameHints) {
		List<VariableName> ret = new ArrayList<>();
		for (String hint : nameHints) {
			VariableName variableName = getFreshName(hint);
			ret.add(variableName);
		}
		return ret;
	}

	public List<VariableName> varDecl(List<String> nameHints, Expression value) {
		List<VariableName> ret = getFreshNames(nameHints);
		List<Expression> names = new ArrayList<>(ret);
		addStatement(new Assignment(names, true, Collections.singletonList(value)));
		return ret;
	}

	public VariableName varDecl(String nameHint, Expression value) {
		return varDecl(Collections.singletonList(nameHint), value).get(0);
	}

	public VariableName varDecl(String nameHint, Type type) {
		VariableName ret = getFreshNames(Collections.singletonList(nameHint)).get(0);
		String name = ret.getName();
		addStatement(new VariableDeclarationStatement(new VariableDeclaration(name, type, null)));
		return ret;
	}

	public VariableName getFreshName(String nameHint) {
		String actualName = nameCleaner.cleanName(nameHint);
		return new VariableName(actualName);
	}

	public void goTo(LabelName name) {
		addStatement(new GoTo(name));
	}

	public void addPanic(Expression e) {
		addStatement(new ExpressionStatement(new Call(new VariableName("panic"), Collections.singletonList(e))));
	}

	public void addStatement(Expression expression) {
		addStatement(new ExpressionStatement(expression));
	}

	@Override
	public void addStatement(Statement s) {
		statements.add(s);
	}

	@Override
	protected void addBlock(Block block) {
		statements.add(block);
	}

	@Override
	protected void addFunction(FunctionDeclaration fn) {
		builder.addFunction(fn);
	}

	@Override
	public void close() {
		onSuccess.action(getBlock());
	}

	@Override
	public TypeName defineType(String nameHint, Type type) {
		return builder.defineType(nameHint, type);
	}

	@Override
	public FunctionDeclarationBuilder defineFunction(UID uid, String nameHint) {
		return builder.defineFunction(uid, nameHint);
	}

	public AnonymousFunctionBuilder anonymousFunction() {
		return new AnonymousFunctionBuilder(this, nameCleaner, nameMap);
	}

	public void goStmt(Expression expression) {
		addStatement(new Go(expression));
	}

	public void deferStmt(Expression expression) {
		addStatement(new Defer(expression));
	}

	public void returnStmt(Expression... values) {
		addStatement(new Return(Arrays.asList(values)));
	}

	public void linkUID(UID uid, VariableName name) {
		nameMap.put(uid, name);
	}

	public VariableName findUID(UID uid) {
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
