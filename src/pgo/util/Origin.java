package pgo.util;

/**
 * 
 * Where something was Derived from. Should be implemented by anything relevant.
 * 
 * The Visitor allows code to inspect what the origin actually was, ideally at a high
 * level.
 *
 */
public interface Origin {
	
	public abstract class Visitor<T>{

		public abstract T visit(SourceLocatable sourceLocatable);
		public abstract T visit(Derived derived);
		
	}
	
	public <T> T accept(Visitor<T> v);
	
}
