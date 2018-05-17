package pgo.model.golang;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

/**
 * Wraps the definition of a Golang struct
 *
 */
public class StructDefinition extends Expression {

    // the struct name
    private String name;

    // are we creating a reference to a struct?
    private boolean reference;

    private Map<String, Expression> fields;

    public StructDefinition(String name, boolean reference) {
        this.name = name;
        this.reference = reference;
        this.fields = new HashMap<>();
    }

    public void addField(String name, Expression val) {
        this.fields.put(name, val);
    }

    @Override
    public List<String> toGo() {
        Vector<String> ret = new Vector<>();
        StringBuilder decl = new StringBuilder(reference ? "&" : "");
        decl.append(name).append("{\n");

        for (Map.Entry<String, Expression> entry : fields.entrySet()) {
            decl.append(entry.getKey()).append(": ").append(entry.getValue().toGo().get(0)).append(",\n");
        }
        decl.append("}");
        ret.add(decl.toString());
        return ret;
    }
}
