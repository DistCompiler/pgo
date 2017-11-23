package pgo.model.golang;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Vector;

public class Switch extends Statement {
    Expression switchExp;
    LinkedHashMap<Expression, Vector<Statement>> cases;
    Vector<Statement> defaultCase;

    public Switch(Expression exp) {
        this.switchExp = exp;
        this.cases = new LinkedHashMap<>();
    }

    public void addCase(Expression exp, Vector<Statement> code) {
        cases.put(exp, code);
    }

    public void addDefaultCase(Vector<Statement> code) {
        defaultCase = code;
    }

    @Override
    public Vector<String> toGo() {
        Vector<String> ret = new Vector<>();
        if (switchExp == null) {
            ret.add("switch {");
        } else {
            ret.add("switch (" + String.join(";", switchExp.toGo()) + ") {");
        }
        for (Map.Entry<Expression, Vector<Statement>> entry: cases.entrySet()) {
            Expression label = entry.getKey();
            Vector<Statement> code = entry.getValue();
            ret.add("case " + String.join(";", label.toGo()) + ":");
            addIndentedAST(ret, code);
        }
        if (defaultCase != null) {
            ret.add("default:");
            addIndentedAST(ret, defaultCase);
        }
        ret.add("}");
        return ret;
    }
}
