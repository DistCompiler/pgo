package pgo.parser;

import java.util.ListIterator;

import pgo.lexer.TLAToken;

public class ParseContext {
	
	ListIterator<TLAToken> iter;
	
	public static class Mark{
		int markedPosition;
		
		public Mark(int markedPosition) {
			this.markedPosition = markedPosition;
		}

		public int getMarkedPosition() {
			return markedPosition;
		}
		
	}
	
	
	public ParseContext(ListIterator<TLAToken> iter) {
		this.iter = iter;
	}

	public Mark mark() {
		return new Mark(iter.nextIndex());
	}
	
	public TLAToken readToken() {
		if(iter.hasNext()) {
			return iter.next();
		}else {
			return null;
		}
	}
	
	public void restore(Mark mark) {
		while(iter.nextIndex() < mark.getMarkedPosition()) {
			iter.next();
		}
		while(iter.nextIndex() > mark.getMarkedPosition()) {
			iter.previous();
		}
	}

}
