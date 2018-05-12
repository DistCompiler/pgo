package pgo.parser;

import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import pcal.TLAToken;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;
import tla2sany.st.Location;

public class ParseTools {
	
	private ParseTools() {}
	
	private static SourceLocation getSourceLocation(TLAToken tok) {
		if(tok.source == null) {
			return SourceLocation.unknown();
		}else {
			Location loc =  tok.source.toLocation();
			return new SourceLocation(Paths.get(loc.source()), loc.beginLine(), loc.endLine(), loc.beginColumn(), loc.endColumn());
		}
	}
	
	public static ParseAction<LocatedString> parseTokenType(int tokenType, int minColumn){
		return ctx -> {
			TLAToken tok = ctx.readToken();
			if(tok == null) {
				return ParseResult.failure(ParseFailure.unexpectedEOF());
			}else if(tok.column < minColumn) {
				return ParseResult.failure(ParseFailure.insufficientlyIndented(tok.column, minColumn, getSourceLocation(tok)));
			}else if(tok.type != tokenType) {
				return ParseResult.failure(ParseFailure.unexpectedTokenType(tok.type, getSourceLocation(tok)));
			}else {
				return ParseResult.success(new LocatedString(tok.string, getSourceLocation(tok)));
			}
		};
	}
	
	public static ParseAction<LocatedString> parseBuiltinToken(String t, int minColumn){
		return parseTokenType(TLAToken.BUILTIN, minColumn)
				.chain(s -> {
					if(s.getValue().equals(t)) {
						return ParseAction.success(s);
					}else {
						return ParseAction.failure(
								ParseFailure.unexpectedBuiltinToken(s, Collections.singletonList(t)));
					}
				});
	}
	
	public static ParseAction<LocatedString> parseBuiltinTokenOneOf(List<String> options, int minColumn){
		return parseTokenType(TLAToken.BUILTIN, minColumn)
				.chain(s -> {
					if(options.contains(s.getValue())) {
						return ParseAction.success(s);
					}else {
						return ParseAction.failure(
								ParseFailure.unexpectedBuiltinToken(s, options));
					}
				});
	}
	
	public static ParseAction<PGoTLAIdentifier> parseIdentifier(int minColumn){
		return parseTokenType(TLAToken.IDENT, minColumn)
				.map(s -> new PGoTLAIdentifier(s.getLocation(), s.getValue()));
	}
	
	public static ParseAction<LocatedString> parseString(int minColumn){
		return parseTokenType(TLAToken.STRING, minColumn);
	}
	
	public static ParseAction<LocatedString> parseNumber(int minColumn){
		return parseTokenType(TLAToken.NUMBER, minColumn);
	}
	
	public static <Result> ParseAction<Result> parseOneOf(List<ParseAction<? extends Result>> options){
		return new ParseActionOneOf<Result>(options);
	}
	
	@SafeVarargs
	public static <Result> ParseAction<Result> parseOneOf(ParseAction<? extends Result>... options){
		return parseOneOf(Arrays.asList(options));
	}
	
	public static <Result extends SourceLocatable> ParseAction<LocatedList<Result>> repeat(ParseAction<Result> element){
		return new ParseActionRepeated<Result>(element);
	}
	
	public static <Result extends SourceLocatable> ParseAction<LocatedList<Result>> repeatOneOrMore(ParseAction<Result> element){
		Mutator<Result> first = new Mutator<>();
		Mutator<LocatedList<Result>> rest = new Mutator<>();
		return sequence(
				part(first, element),
				part(rest, repeat(element))
				).map(seqResult -> {
					rest.getValue().addLocation(seqResult.getLocation());
					rest.getValue().add(0, first.getValue());
					return rest.getValue();
				});
	}
	
	public static ParseAction<ParseActionSequenceResult> sequence(List<ParseActionSequence.Part> parts){
		return new ParseActionSequence(parts);
	}
	
	public static ParseAction<ParseActionSequenceResult> sequence(ParseActionSequence.Part... parts){
		return sequence(Arrays.asList(parts));
	}
	
	public static <Result extends SourceLocatable> ParseActionSequence.Part part(Mutator<Result> mutator, ParseAction<Result> action){
		return ParseActionSequence.part(mutator, action);
	}
	
	public static <Result extends SourceLocatable> ParseActionSequence.Part drop(ParseAction<Result> action){
		return ParseActionSequence.part(new DropMutator<Result>(), action);
	}
	
	public static ParseAction<Void> nop(){
		return ParseAction.success(null);
	}

}
