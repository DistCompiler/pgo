package pgo;

public class ProcessStringArg extends ProcessArg {
    private String value;

    public ProcessStringArg(String val) {
        value = val;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof ProcessStringArg)) {
            return false;
        }
        ProcessStringArg other = (ProcessStringArg) o;
        return this.value.equals(other.getValue());
    }

    @Override
    public String toString() {
        return "ProcessStringArg(" + value + ")";
    }

    public String getValue() {
        return value;
    }
}
