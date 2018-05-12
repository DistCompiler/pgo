package pgo.parser;

import java.util.ListIterator;

import pcal.TLAToken;
import pgo.util.SourceLocation;

// ParseAction -> success / failure ; chainable (sequence of discrete actions with results)
// 		; composable (a chain can be used as part of a larger action)
// 		; repeatable (if we need to loop on the result of an action we can do it)
//		; possible to use as lookahead (i.e failure can be trivially reacted to)
// BranchingParse(if, else); (or series of options)

public class ParseContext {
	
	ListIterator<TLAToken> iter;
	SourceLocation lastKnownPosition;
	
	public static class Mark{
		int markedPosition;
		SourceLocation lastKnownPosition;
		
		public Mark(int markedPosition, SourceLocation lastKnownPosition) {
			this.markedPosition = markedPosition;
			this.lastKnownPosition = lastKnownPosition;
		}

		public int getMarkedPosition() {
			return markedPosition;
		}

		public SourceLocation getLastKnownPosition() {
			return lastKnownPosition;
		}
		
	}
	
	
	public ParseContext(ListIterator<TLAToken> iter) {
		this.iter = iter;
		this.lastKnownPosition = null;
	}

	public Mark mark() {
		return new Mark(iter.nextIndex(), lastKnownPosition);
	}
	
	public TLAToken readToken() {
		TLAToken tok = null;
		while(iter.hasNext() &&(tok = iter.next()) == null);
		return tok;
	}
	
	public void restore(Mark mark) {
		while(iter.nextIndex() < mark.getMarkedPosition()) {
			iter.next();
		}
		while(iter.nextIndex() > mark.getMarkedPosition()) {
			iter.previous();
		}
		lastKnownPosition = mark.getLastKnownPosition();
	}

}
