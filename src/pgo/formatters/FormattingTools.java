package pgo.formatters;

import java.io.IOException;
import java.io.Writer;
import java.util.List;

public class FormattingTools {
	
	private FormattingTools() {}
	
	public interface Formatter<T>{
		void format(T param) throws IOException;
	}
	
	public static <T> void writeCommaSeparated(Writer out, List<T> items, Formatter<T> writer) throws IOException {
		boolean isFirst = true;
		for(T item : items) {
			if(!isFirst) {
				out.write(",");
			}
			isFirst = false;
			writer.format(item);
		}
	}

}
