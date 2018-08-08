package pgo.parser;

import pgo.util.SourceLocatable;

import javax.xml.transform.Source;
import java.util.function.Function;

public class MappingParseAction<Src extends SourceLocatable, Dst extends SourceLocatable> extends ParseAction {

	int location;
	private Function<Src, Dst> mapping;

	public MappingParseAction(int location, Function<Src, Dst> mapping) {
		this.location = location;
		this.mapping = mapping;
	}

	public int getLocation() { return location; }
	public Function<Src, Dst> getMapping() { return mapping; }

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
