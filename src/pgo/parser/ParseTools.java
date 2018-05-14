package pgo.parser;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import pgo.lexer.TLAToken;
import pgo.lexer.TLATokenType;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.util.SourceLocatable;

public class ParseTools {
	
	private ParseTools() {}
	
	/*private static SourceLocation getSourceLocation(TLAToken tok) {
		if(tok.source == null) {
			return SourceLocation.unknown();
		}else {
			PCalLocation begin = tok.source.getBegin();
			PCalLocation end = tok.source.getEnd();
			return new SourceLocation(
					Paths.get("???"), begin.getLine(), end.getLine(), begin.getColumn(), end.getColumn());
		}
	}*/
	
	public static ParseAction<LocatedString> parseTokenType(TLATokenType tokenType, int minColumn){
		return ctx -> {
			TLAToken tok = ctx.readToken();
			if(tok == null) {
				return ParseResult.failure(ParseFailure.unexpectedEOF());
			}else if(tok.getLocation().getStartColumn() < minColumn) {
				return ParseResult.failure(ParseFailure.insufficientlyIndented(minColumn, tok.getLocation()));
			}else if(tok.getType() != tokenType) {
				return ParseResult.failure(ParseFailure.unexpectedTokenType(tok.getType(), tok.getLocation()));
			}else {
				return ParseResult.success(new LocatedString(tok.getValue(), tok.getLocation()));
			}
		};
	}
	
	public static ParseAction<LocatedString> parseBuiltinToken(String t, int minColumn){
		return parseTokenType(TLATokenType.BUILTIN, minColumn)
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
		return parseTokenType(TLATokenType.BUILTIN, minColumn)
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
		return parseTokenType(TLATokenType.IDENT, minColumn)
				.map(s -> new PGoTLAIdentifier(s.getLocation(), s.getValue()));
	}
	
	public static ParseAction<LocatedString> parseString(int minColumn){
		return parseTokenType(TLATokenType.STRING, minColumn);
	}
	
	public static ParseAction<LocatedString> parseNumber(int minColumn){
		return parseTokenType(TLATokenType.NUMBER, minColumn);
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
