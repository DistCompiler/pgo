package pgo;

public class ProcessIntArg extends ProcessArg {
    private int value;

    public ProcessIntArg(int val) {
        value = val;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof ProcessIntArg)) {
            return false;
        }
        ProcessIntArg other = (ProcessIntArg) o;
        return this.value == other.getValue();
    }

    @Override
    public String toString() {
        return "ProcessIntArg(" + value + ")";
    }

    public int getValue() {
        return value;
    }
}
