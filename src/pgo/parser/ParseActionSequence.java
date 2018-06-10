package pgo.parser;

import java.util.List;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public class ParseActionSequence implements ParseAction<ParseActionSequenceResult> {
	
	private static class PartResult{
		ParseFailure failure;
		SourceLocation sourceLocation;
		
		public PartResult(ParseFailure failure, SourceLocation sourceLocation) {
			this.failure = failure;
			this.sourceLocation = sourceLocation;
		}

		public ParseFailure getFailure() {
			return failure;
		}
		
		public boolean isNull() {
			return failure == null && sourceLocation == null;
		}

		public SourceLocation getSourceLocation() {
			return sourceLocation;
		}
	}
	
	public interface Part{
		public PartResult perform(ParseContext ctx);
	}
	
	public static class TypedPart<Result extends SourceLocatable> implements Part{
		MutatorInterface<Result> mutator;
		ParseAction<Result> action;
		public TypedPart(MutatorInterface<Result> mutator, ParseAction<Result> action) {
			this.mutator = mutator;
			this.action = action;
		}
		
		@Override
		public PartResult perform(ParseContext ctx) {
			ParseResult<Result> result = action.perform(ctx);
			if(result.isSuccess()) {
				mutator.setValue(result.getSuccess());
				if(result.getSuccess() != null) {
					return new PartResult(null, result.getSuccess().getLocation());
				}else {
					return new PartResult(null, null); // allows use of null results, on the
													   // condition they represent none of the source
				}
			}else {
				return new PartResult(result.getFailure(), null);
			}
		}
	}

	public static <Result extends SourceLocatable> TypedPart<Result> part(MutatorInterface<Result> mutator, ParseAction<Result> action){
		return new TypedPart<Result>(mutator, action);
	}
	
	List<Part> parts;
	
	public ParseActionSequence(List<Part> parts) {
		this.parts = parts;
	}

	@Override
	public ParseResult<ParseActionSequenceResult> perform(ParseContext ctx) {
		SourceLocation overallLocation = SourceLocation.unknown();
		for(Part part : parts) {
			PartResult result = part.perform(ctx);
			if(result.getFailure() != null) {
				return ParseResult.failure(result.getFailure());
			}else if(!result.isNull()) {
				overallLocation = overallLocation.combine(result.getSourceLocation());
			}
		}
		return ParseResult.success(new ParseActionSequenceResult(overallLocation));
	}

}
