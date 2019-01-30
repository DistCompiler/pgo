package pgo.parser;

import pgo.formatters.IndentingWriter;
import pgo.formatters.ParseFailureFormattingVisitor;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Objects;
import java.util.regex.Pattern;

public abstract class ParseFailure {

	@Override
	public abstract boolean equals(Object other);

	@Override
	public abstract int hashCode();
	
	public abstract <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E;
	
	@Override
	public String toString() {
		StringWriter w = new StringWriter();
		IndentingWriter out = new IndentingWriter(w);
		try{
			accept(new ParseFailureFormattingVisitor(out));
		} catch (IOException e1) {
			throw new RuntimeException("string writers should not throw IO exceptions", e1);
		}
		return w.toString();
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

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			StringMatchFailure that = (StringMatchFailure) o;
			return Objects.equals(location, that.location) &&
					Objects.equals(string, that.string);
		}

		@Override
		public int hashCode() {
			return Objects.hash(location, string);
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

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			PatternMatchFailure that = (PatternMatchFailure) o;
			return Objects.equals(location, that.location) &&
					Objects.equals(pattern, that.pattern);
		}

		@Override
		public int hashCode() {

			return Objects.hash(location, pattern);
		}
	}

	public static PatternMatchFailure patternMatchFailure(SourceLocation location, Pattern pattern) {
		return new PatternMatchFailure(location, pattern);
	}

	public static ParseFailure eofMatchFailure() {
		return new EOFMatchFailure();
	}

	public static class EOFMatchFailure extends ParseFailure {
		@Override
		public boolean equals(Object other) {
			return other instanceof EOFMatchFailure;
		}

		@Override
		public int hashCode() {
			return 0;
		}

		@Override
		public <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E {
			return v.visit(this);
		}
	}

	public static class RejectFailure<Result extends SourceLocatable> extends ParseFailure {
		private final Grammar<Result> toReject;

		public RejectFailure(Grammar<Result> toReject) {
			this.toReject = toReject;
		}

		public Grammar<Result> getToReject() {
			return toReject;
		}

		@Override
		public <T, E extends Throwable> T accept(ParseFailureVisitor<T, E> v) throws E {
			return v.visit(this);
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			RejectFailure<Result> that = (RejectFailure<Result>) o;
			return Objects.equals(toReject, that.toReject);
		}

		@Override
		public int hashCode() {
			return Objects.hash(toReject);
		}
	}

	public static <Result extends SourceLocatable> ParseFailure rejectFailure(Grammar<Result> toReject) {
		return new RejectFailure<>(toReject);
	}
}
