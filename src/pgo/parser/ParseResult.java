package pgo.parser;

public abstract class ParseResult<Result> {
	
	public static class Success<SuccessResult> extends ParseResult<SuccessResult> {

		SuccessResult result;
		
		public Success(SuccessResult result) {
			this.result = result;
		}
		
		@Override
		public boolean isSuccess() {
			return true;
		}

		@Override
		public SuccessResult getSuccess() {
			return result;
		}

		@Override
		public ParseFailure getFailure() {
			throw new RuntimeException("Tried to get failure of successful parse result "+result);
		}

	}

	private static class Failure<Any> extends ParseResult<Any>{
		
		ParseFailure failure;
		
		public Failure(ParseFailure failure) {
			this.failure = failure;
		}

		@Override
		public boolean isSuccess() {
			return false;
		}

		@Override
		public Any getSuccess() {
			throw new RuntimeException("Parse result was failure " + failure + " cannot get result");
		}

		@Override
		public ParseFailure getFailure() {
			return failure;
		}
		
	}
	
	public abstract boolean isSuccess();
	public abstract Result getSuccess();
	public abstract ParseFailure getFailure();
	
	public static <Result> Success<Result> success(Result result){
		return new Success<>(result);
	}
	
	public static <Any> Failure<Any> failure(ParseFailure f) {
		return new Failure<>(f);
	}

}
