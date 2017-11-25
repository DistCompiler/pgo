package pgo.model.golang;

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

/**
 * Assigns a value to a variable while declaring it:
 *
 *
 *  goVar := {expr}
 *
 */
public class Assignment extends Statement {

    // the variable name(s)
    private Vector<String> lhs;

    // right hand side expression
    private Expression expr;

    public Assignment(Vector<String> names, Expression val) {
        this.lhs = names;
        this.expr = val;
    }

    @Override
    public Vector<String> toGo() {
        Vector<String> ret = new Vector<>();
        String decl;

        decl = String.format("%s := %s", String.join(", ", this.lhs), expr.toGo().get(0));
        ret.add(decl);
        return ret;
    }
}
