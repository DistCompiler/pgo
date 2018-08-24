package pgo.trans.passes.tlagen;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.pcal.*;
import pgo.model.tla.*;
import pgo.model.tla.builder.TLAConjunctBuilder;
import pgo.model.tla.builder.TLADisjunctBuilder;
import pgo.model.tla.builder.TLAIfBuilder;
import pgo.model.tla.builder.TLAOperatorBuilder;
import pgo.util.Mutator;
import pgo.util.SourceLocation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class PlusCalStatementTranslationVisitor extends PlusCalStatementVisitor<PlusCalStatementTranslationVisitor.PrevStatementType, RuntimeException> {

	private final TLAConjunctBuilder builder;
	private final TranslationContext translationContext;
	private final PrevStatementType prevStatementType;
	private final Continuation continuation;

	public final static class PrevStatementType {
		private final boolean call;
		private final boolean label;
		private final boolean requireLabel;
		private final boolean containsLabelCallReturnOrGoto_;
		private final PlusCalLabel prevLabel;

		public PrevStatementType(boolean call, boolean label, boolean requireLabel, boolean containsLabelCallReturnOrGoto_, PlusCalLabel prevLabel) {
			this.call = call;
			this.label = label;
			this.requireLabel = requireLabel;
			this.containsLabelCallReturnOrGoto_ = containsLabelCallReturnOrGoto_;
			this.prevLabel = prevLabel;
		}

		public PrevStatementType(PlusCalLabel prevLabel) {
			this(false, true, false, true, prevLabel);
		}

		public PrevStatementType(boolean call, boolean label, boolean requireLabel, boolean containsLabelCallReturnOrGoto_) {
			this(call, label, requireLabel, containsLabelCallReturnOrGoto_, null);
		}

		public boolean isCall() {
			return call;
		}

		public boolean isLabel() {
			return label;
		}

		public boolean requiresLabel() {
			return requireLabel;
		}

		public PlusCalLabel getPrevLabel() {
			return prevLabel;
		}

		public boolean containsLabelCallReturnOrGoto() { return containsLabelCallReturnOrGoto_; }
	}

	public interface Continuation {
		PrevStatementType perform(TLAConjunctBuilder builder, TranslationContext translationContext, PrevStatementType prevStatementType);
	}

	private static final Continuation NOP_CONTINUATION = (_1, _2, prevStatementType) -> prevStatementType;

	public PlusCalStatementTranslationVisitor(TLAConjunctBuilder builder, TranslationContext translationContext,
											  PrevStatementType prevStatementType, Continuation continuation) {
		this.builder = builder;
		this.translationContext = translationContext;
		this.prevStatementType = prevStatementType;
		this.continuation = continuation;
	}

	public PrevStatementType visitProcessBody(List<PlusCalStatement> stmts) {
		return new StatementListContinuation(stmts, (innerBuilder, tc, prevStatementType) -> {
			innerBuilder.addExpression(new TLABinOp(
					SourceLocation.unknown(),
					new TLASymbol(SourceLocation.unknown(), "="),
					Collections.emptyList(),
					new TLAUnary(
							SourceLocation.unknown(),
							new TLASymbol(SourceLocation.unknown(), "'"),
							Collections.emptyList(),
							tc.getPCLHS()),
					new TLAString(SourceLocation.unknown(), "Done")
			));
			innerBuilder.addExpression(tc.getUNCHANGED());
			return new PrevStatementType(false, false, true, true);
		}).perform(builder, translationContext, prevStatementType);
	}

	@Override
	public PrevStatementType visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		builder.addExpression(new TLABinOp(
				labeledStatements.getLabel().getLocation(),
				new TLASymbol(SourceLocation.unknown(), "="),
				Collections.emptyList(),
				new TLAUnary(
						SourceLocation.unknown(),
						new TLASymbol(SourceLocation.unknown(), "'"),
						Collections.emptyList(),
						translationContext.getPCLHS()),
				new TLAString(SourceLocation.unknown(), labeledStatements.getLabel().getName())));
		builder.addExpression(translationContext.getUNCHANGED());

		TranslationContext nextContext = translationContext.getLabelTranslationContext();

		try(TLAOperatorBuilder def = builder.operatorDefinition(labeledStatements.getLabel().getName())) {
			nextContext.addLabelOperatorArguments(def);
			try (TLAConjunctBuilder bodyBuilder = def.getConjunctBuilder()) {
				return new StatementListContinuation(labeledStatements.getStatements(), continuation)
						.perform(bodyBuilder, nextContext, new PrevStatementType(labeledStatements.getLabel()));
			}
		}
	}

	private static final class WhileBodyContinuation implements Continuation {

		private final List<PlusCalStatement> body;
		private final String headLabel;

		public WhileBodyContinuation(List<PlusCalStatement> body, String headLabel) {
			this.body = body;
			this.headLabel = headLabel;
		}

		@Override
		public PrevStatementType perform(TLAConjunctBuilder builder, TranslationContext translationContext, PrevStatementType prevStatementType) {
			if(body.isEmpty()) {
				//if(prevStatementType.requiresLabel()) throw new InternalCompilerError();
				builder.addExpression(new TLABinOp(
						SourceLocation.unknown(),
						new TLASymbol(SourceLocation.unknown(), "="),
						Collections.emptyList(),
						translationContext.getPCLHS(),
						new TLAString(SourceLocation.unknown(), headLabel)));
				builder.addExpression(translationContext.getUNCHANGED());
				return new PrevStatementType(false, false, true, false);
			}else {
				return body.get(0).accept(new PlusCalStatementTranslationVisitor(
						builder,
						translationContext,
						prevStatementType,
						new WhileBodyContinuation(
								body.subList(1, body.size()), headLabel)));
			}
		}
	}

	@Override
	public PrevStatementType visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		if(!prevStatementType.isLabel()) {
			throw new InternalCompilerError();
		}
		try(TLAIfBuilder wBuilder = builder.ifexp(plusCalWhile.getCondition())) {
			boolean containsLabelCallReturnOrGoto;
			try (TLAConjunctBuilder whenTrue = wBuilder.getWhenTrueBuilder()) {
				containsLabelCallReturnOrGoto = new WhileBodyContinuation(
						plusCalWhile.getBody(),
						prevStatementType.getPrevLabel().getName())
						.perform(whenTrue, translationContext.getChild(), prevStatementType)
						.containsLabelCallReturnOrGoto();
			}
			try (TLAConjunctBuilder whenFalse = wBuilder.getWhenFalseBuilder()) {
				containsLabelCallReturnOrGoto |= continuation.perform(whenFalse, translationContext, prevStatementType)
						.containsLabelCallReturnOrGoto();
			}
			return new PrevStatementType(false, false, false, containsLabelCallReturnOrGoto);
		}
	}

	private static final class StatementListContinuation implements Continuation {

		private final List<PlusCalStatement> body;
		private final Continuation continuation;

		public StatementListContinuation(List<PlusCalStatement> body, Continuation continuation) {
			this.body = body;
			this.continuation = continuation;
		}

		@Override
		public PrevStatementType perform(TLAConjunctBuilder builder, TranslationContext translationContext, PrevStatementType prevStatementType) {
			if(!body.isEmpty()) {
				return body.get(0).accept(new PlusCalStatementTranslationVisitor(
						builder,
						translationContext,
						prevStatementType,
						new StatementListContinuation(body.subList(1, body.size()), continuation)));
			}else{
				return continuation.perform(builder, translationContext, prevStatementType);
			}
		}
	}

	@Override
	public PrevStatementType visit(PlusCalIf plusCalIf) throws RuntimeException {
		if(prevStatementType.requiresLabel()) throw new RuntimeException();

		PrevStatementType lhsResult, rhsResult;
		try(TLAIfBuilder ifBuilder = builder.ifexp(plusCalIf.getCondition())){
			TranslationContext lChild = translationContext.getChild();
			TranslationContext rChild = translationContext.getChild();
			try(TLAConjunctBuilder whenTrue = ifBuilder.getWhenTrueBuilder()) {
				lhsResult = new StatementListContinuation(plusCalIf.getYes(), NOP_CONTINUATION)
						.perform(whenTrue, lChild, prevStatementType);
				try(TLAConjunctBuilder whenFalse = ifBuilder.getWhenFalseBuilder()) {
					rhsResult = new StatementListContinuation(plusCalIf.getNo(), NOP_CONTINUATION)
							.perform(whenFalse, rChild, prevStatementType);
					whenFalse.addExpression(rChild.getRelativeUNCHANGED(lChild));
				}
				whenTrue.addExpression(lChild.getRelativeUNCHANGED(rChild));
			}
			translationContext.mergeUNCHANGED(lChild);
			translationContext.mergeUNCHANGED(rChild);
		}
		boolean containsLabelCallReturnOrGoto = lhsResult.containsLabelCallReturnOrGoto()
				|| rhsResult.containsLabelCallReturnOrGoto();
		return continuation.perform(builder, translationContext, new PrevStatementType(
				false, false, containsLabelCallReturnOrGoto, containsLabelCallReturnOrGoto));
	}

	@Override
	public PrevStatementType visit(PlusCalEither plusCalEither) throws RuntimeException {
		if(prevStatementType.requiresLabel()) throw new InternalCompilerError();

		boolean containsCallReturnOrGoto = false;
		try(TLADisjunctBuilder eBuilder = builder.disjunct()) {
			for(List<PlusCalStatement> stmts : plusCalEither.getCases()) {
				try(TLAConjunctBuilder caseBuilder = eBuilder.conjunct()) {
					PrevStatementType tp = new StatementListContinuation(stmts, NOP_CONTINUATION)
							.perform(caseBuilder, translationContext.getChild(), prevStatementType);
					containsCallReturnOrGoto |= tp.containsLabelCallReturnOrGoto();
				}
			}
		}
		return continuation.perform(builder, translationContext, new PrevStatementType(
				false, false, containsCallReturnOrGoto, containsCallReturnOrGoto));
	}

	private static final class WriteContinuation implements Continuation {

		private final List<PlusCalAssignmentPair> pairs;
		private final Continuation continuation;

		public WriteContinuation(List<PlusCalAssignmentPair> pairs, Continuation continuation) {
			this.pairs = pairs;
			this.continuation = continuation;
		}

		@Override
		public PrevStatementType perform(TLAConjunctBuilder builder, TranslationContext translationContext, PrevStatementType prevStatementType) {
			if(pairs.isEmpty()) {
				return continuation.perform(builder, translationContext, prevStatementType);
			}else{
				return translationContext.buildVariableWrite(
						builder,
						pairs.get(0),
						prevStatementType,
						new WriteContinuation(pairs.subList(1, pairs.size()), continuation));
			}
		}
	}

	@Override
	public PrevStatementType visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		if(prevStatementType.requiresLabel()) throw new InternalCompilerError();

		// TODO: a.a := 1 || a.b := 2
		return new WriteContinuation(plusCalAssignment.getPairs(), continuation)
				.perform(builder, translationContext, prevStatementType);
	}

	@Override
	public PrevStatementType visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PrevStatementType visit(PlusCalSkip skip) throws RuntimeException {
		if(prevStatementType.requiresLabel()) throw new InternalCompilerError();

		builder.addExpression(new TLABool(SourceLocation.unknown(), true));
		return continuation.perform(builder, translationContext, new PrevStatementType(
				false,
				false,
				false,
				prevStatementType.containsLabelCallReturnOrGoto()));
	}

	@Override
	public PrevStatementType visit(PlusCalCall plusCalCall) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PrevStatementType visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable(); // macros should already be expanded
	}

	@Override
	public PrevStatementType visit(PlusCalWith with) throws RuntimeException {
		if(prevStatementType.requiresLabel()) throw new InternalCompilerError();

		// with must not contain any labels
		List<TLAUnit> vars = new ArrayList<>();
		for(PlusCalVariableDeclaration decl : with.getVariables()) {
			vars.add(new TLAOperatorDefinition(
					SourceLocation.unknown(),
					new TLAIdentifier(SourceLocation.unknown(), decl.getName().getValue()),
					Collections.emptyList(),
					decl.getValue(),
					false));
		}
		Mutator<TLAExpression> body = new Mutator<>();
		PrevStatementType pType;
		try(TLAConjunctBuilder bodyBuilder = new TLAConjunctBuilder(builder.getParent(), body::setValue)) {
			pType = new StatementListContinuation(with.getBody(), NOP_CONTINUATION)
					.perform(bodyBuilder, translationContext, prevStatementType);
		}
		builder.addExpression(new TLALet(SourceLocation.unknown(), vars, body.getValue()));
		return continuation.perform(builder, translationContext, pType);
	}

	@Override
	public PrevStatementType visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		if(prevStatementType.requiresLabel()) throw new InternalCompilerError();

		builder.addExpression(new TLAOperatorCall(
				SourceLocation.unknown(),
				new TLAIdentifier(SourceLocation.unknown(), "PrintT"),
				Collections.emptyList(),
				Collections.singletonList(plusCalPrint.getValue())));
		return continuation.perform(builder, translationContext, new PrevStatementType(
				false,
				false,
				false,
				prevStatementType.containsLabelCallReturnOrGoto()));
	}

	@Override
	public PrevStatementType visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		if(prevStatementType.requiresLabel()) throw new InternalCompilerError();

		builder.addExpression(new TLAOperatorCall(
				SourceLocation.unknown(),
				new TLAIdentifier(SourceLocation.unknown(), "Assert"),
				Collections.emptyList(),
				Arrays.asList(
						plusCalAssert.getCondition(),
						new TLAString(
								SourceLocation.unknown(),
								String.format(
										"Failure of assertion at line %1$d, column %2$d.",
										plusCalAssert.getLocation().getStartLine(),
										plusCalAssert.getLocation().getStartColumn()))
				)));
		return continuation.perform(builder, translationContext, new PrevStatementType(
				false,
				false,
				false,
				prevStatementType.containsLabelCallReturnOrGoto()));
	}

	@Override
	public PrevStatementType visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		builder.addExpression(plusCalAwait.getCondition());
		return continuation.perform(builder, translationContext, new PrevStatementType(
				false,
				false,
				false,
				prevStatementType.containsLabelCallReturnOrGoto()));
	}

	@Override
	public PrevStatementType visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		builder.addExpression(new TLABinOp(
				SourceLocation.unknown(),
				new TLASymbol(SourceLocation.unknown(), "="),
				Collections.emptyList(),
				new TLAUnary(
						SourceLocation.unknown(),
						new TLASymbol(SourceLocation.unknown(), "'"),
						Collections.emptyList(),
						translationContext.getPCLHS()),
				new TLAString(SourceLocation.unknown(), plusCalGoto.getTarget())));
		builder.addExpression(translationContext.getUNCHANGED());
		return continuation.perform(builder, translationContext, new PrevStatementType(
				false,
				false,
				true,
				true));
	}
}
