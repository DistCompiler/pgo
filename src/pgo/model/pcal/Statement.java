package pgo.model.pcal;

import pgo.util.SourceLocation;

public abstract class Statement extends Node {
	
	public Statement(SourceLocation location) {
		super(location);
	}
	
	public abstract class Visitor<T>{
		public abstract T visit(LabeledStatements labeledStatements);
		public abstract T visit(While while1);
		public abstract T visit(If if1);
		public abstract T visit(Either either);
		public abstract T visit(Assignment assignment);
		public abstract T visit(Return return1);
		public abstract T visit(Skip skip);
		public abstract T visit(Call call);
		public abstract T visit(MacroCall macroCall);
		public abstract T visit(With with);
		public abstract T visit(Print print);
		public abstract T visit(Assert assert1);
		public abstract T visit(Await await);
		public abstract T visit(Goto goto1);
	}
	
	public abstract <T> T accept(Visitor<T> v);

}
