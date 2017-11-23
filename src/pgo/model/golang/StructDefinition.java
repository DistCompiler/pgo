package pgo.model.golang;

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

/**
 * Wraps the definition of a Golang struct
 *
 */
public class StructDefinition extends Statement {

    // the struct name
    private String name;

    // are we creating a reference to a struct?
    private boolean reference;

    private HashMap<String, Expression> fields;

    public StructDefinition(String name, boolean reference) {
        this.name = name;
        this.reference = reference;
        this.fields = new HashMap<>();
    }

    public void addField(String name, Expression val) {
        this.fields.put(name, val);
    }

    @Override
    public Vector<String> toGo() {
        Vector<String> ret = new Vector<>();
        String decl = reference ? "&" : "";
        decl += String.format("%s{", name);

        for (Map.Entry<String, Expression> entry : fields.entrySet()) {
            decl += String.format("%s: %s,", entry.getKey(), entry.getValue().toGo().get(0));
        }
        decl += "}";

        ret.add(decl);
        return ret;
    }
}
