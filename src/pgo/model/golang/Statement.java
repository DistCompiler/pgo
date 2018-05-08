package pgo.model.golang;

/**
 * A go code statement
 *
 */
public abstract class Statement {
	
	public abstract class Visitor<T>{

		public abstract T visit(Comment comment);
		public abstract T visit(Assignment assignment);
		public abstract T visit(Return return1);
		public abstract T visit(Block block);
		public abstract T visit(For for1);
		public abstract T visit(If if1);
		public abstract T visit(Switch switch1);
		public abstract T visit(Label label);
		public abstract T visit(GoCall goCall);
		public abstract T visit(Select select);
		
	}
	
	public abstract <T> T accept(Visitor<T> v);

}
