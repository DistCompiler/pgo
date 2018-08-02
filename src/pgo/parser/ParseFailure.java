package pgo.parser;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import pgo.formatters.IndentingWriter;
import pgo.formatters.ParseActionContextFormattingVisitor;
import pgo.formatters.ParseFailureFormattingVisitor;
import pgo.util.SourceLocation;

public abstract class ParseFailure {
	
	private List<ActionContext> context;
	
	public ParseFailure() {
		this.context = new ArrayList<>();
	}
	
	public List<ActionContext> getContext() {
		return context;
	}
	
	public void addContext(ActionContext ctx) {
		context.add(ctx);
	}
	
	public abstract <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E;
	
	@Override
	public String toString() {
		ParseFailureOrderingVisitor v = new ParseFailureOrderingVisitor();
		accept(v);
		StringWriter w = new StringWriter();
		IndentingWriter out = new IndentingWriter(w);
		boolean first = true;
		for(Map.Entry<SourceLocation, List<ParseFailure>> e : v.getFailures().entrySet()) {
			try {
				if(first) {
					first = false;
				}else {
					out.newLine();
				}
				out.write("Parse failure at line " + e.getKey().getStartLine() + " column " + e.getKey().getStartColumn() + ":");
				try(IndentingWriter.Indent i_ = out.indent()){
					for(ParseFailure f : e.getValue()) {
						out.newLine();
						f.accept(new ParseFailureFormattingVisitor(out));
						try(IndentingWriter.Indent ii_ = out.indent()){
							for(ActionContext ctx : f.getContext()) {
								out.newLine();
								ctx.accept(new ParseActionContextFormattingVisitor(out));
							}
						}
					}
				}
			} catch (IOException e1) {
				throw new RuntimeException("string writers should not throw IO exceptions", e1);
			}
		}
		return w.toString();
	}
	
	public static class UnexpectedEOF extends ParseFailure {

		@Override
		public <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E {
			return v.visit(this);
		}
		
	}
	
	public static UnexpectedEOF unexpectedEOF() {
		return new UnexpectedEOF();
	}
	
	public static class NoBranchesMatched extends ParseFailure {
		private List<ParseFailure> failures;

		public NoBranchesMatched(List<ParseFailure> failures) {
			this.failures = failures;
		}

		public List<ParseFailure> getFailures() {
			return failures;
		}

		@Override
		public <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E {
			return v.visit(this);
		}
	}

	public static NoBranchesMatched noBranchesMatched(List<ParseFailure> failures) {
		return new NoBranchesMatched(failures);
	}
	
	public static class InsufficientlyIndented extends ParseFailure {
		private int minColumn;
		private SourceLocation sourceLocation;
		
		public InsufficientlyIndented(int minColumn, SourceLocation sourceLocation) {
			this.minColumn = minColumn;
			this.sourceLocation = sourceLocation;
		}
		
		public int getMinColumn() {
			return minColumn;
		}

		public SourceLocation getSourceLocation() {
			return sourceLocation;
		}

		@Override
		public <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E {
			return v.visit(this);
		}
	}

	public static InsufficientlyIndented insufficientlyIndented(int minColumn, SourceLocation sourceLocation) {
		return new InsufficientlyIndented(minColumn, sourceLocation);
	}
	
	public static class InsufficientOperatorPrecedence extends ParseFailure{
		private int actualPrecedence;
		private int requiredPrecedence;
		private SourceLocation sourceLocation;
		
		public InsufficientOperatorPrecedence(int actualPrecedence, int requiredPrecedence,
				SourceLocation sourceLocation) {
			this.actualPrecedence = actualPrecedence;
			this.requiredPrecedence = requiredPrecedence;
			this.sourceLocation = sourceLocation;
		}
		
		public int getActualPrecedence() {
			return actualPrecedence;
		}

		public int getRequiredPrecedence() {
			return requiredPrecedence;
		}

		public SourceLocation getSourceLocation() {
			return sourceLocation;
		}

		@Override
		public <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E {
			return v.visit(this);
		}
		
	}
	
	public static InsufficientOperatorPrecedence insufficientOperatorPrecedence(int actualPrecedence, int requiredPrecedence, SourceLocation sourceLocation) {
		return new InsufficientOperatorPrecedence(actualPrecedence, requiredPrecedence, sourceLocation);
	}

	public static class StringMatchFailure extends ParseFailure{

		private SourceLocation location;
		private String string;

		public StringMatchFailure(SourceLocation location, String string){
			this.location = location;
			this.string = string;
		}

		public SourceLocation getLocation() {
			return location;
		}

		public String getString(){
			return string;
		}

		@Override
		public <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E {
			return v.visit(this);
		}
	}

	public static StringMatchFailure stringMatchFailure(SourceLocation location, String string) {
		return new StringMatchFailure(location, string);
	}

	public static class PatternMatchFailure extends ParseFailure{

		private SourceLocation location;
		private Pattern pattern;

		public PatternMatchFailure(SourceLocation location, Pattern pattern){
			this.location = location;
			this.pattern = pattern;
		}

		public SourceLocation getLocation(){
			return location;
		}

		public Pattern getPattern(){
			return pattern;
		}

		@Override
		public <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E {
			return v.visit(this);
		}
	}

	public static PatternMatchFailure patternMatchFailure(SourceLocation location, Pattern pattern) {
		return new PatternMatchFailure(location, pattern);
	}

	public static class ParseSuccess extends ParseFailure {
		@Override
		public <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E {
			return v.visit(this);
		}
	}

	public static ParseSuccess parseSuccess() { return new ParseSuccess(); }

}
