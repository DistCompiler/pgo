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

    // are we declaring a new variable in this assignment
    private boolean declaration;

    public Assignment(Vector<String> names, Expression val, boolean declaration) {
        this.lhs = names;
        this.expr = val;
        this.declaration = declaration;
    }

    @Override
    public Vector<String> toGo() {
        Vector<String> ret = new Vector<>();
        String decl;
        String op = declaration ? ":=" : "=";

        decl = String.format("%s %s %s", String.join(", ", this.lhs), op, expr.toGo().get(0));
        ret.add(decl);
        return ret;
    }
}
