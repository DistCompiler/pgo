---- MODULE ProcedureSpaghetti ----
EXTENDS TLC, Sequences, Integers

(* --mpcal ProcedureSpaghetti {

procedure Proc1(ref a, b)
    variables c;
{
    Proc1lbl1:
        call Proc2(ref a);
    Proc1lbl2:
        a := a + b;
        return;
}

procedure Proc2(ref a_) {
    Proc2lbl1:
        a_ := a_ + 1;
        return;
}

procedure RecursiveProcRef(ref X) {
    RecursiveProclbl1:
        print X;
        call RecursiveProcRef(ref X);
        return;
}

mapping macro M {
    read {
        yield $variable + 1;
    }
    write {
        yield $value - 1;
    }
}

archetype Arch1(ref e, f) {
    Arch1lbl:
        call Proc1(ref e, f);
}

variables V1, V2;

process (Pross1 = 1) == instance Arch1(ref V1, 30)
    mapping V1 via M;

process (Pross2 = 2) == instance Arch1(ref V1, 40);

process (Pross3 = 3) == instance Arch1(ref V2, 50);

process (Pross3Bis = 33) == instance Arch1(ref V2, 60);

process (Pross4 = 4)
    variables c;
{
    Prosslbl1:
        call Proc1(ref c, 10);
    Prosslbl2:
        call Proc1(ref V1, 20);
}

process (Pross5 = 5) {
    Pross5lbl1:
        call RecursiveProcRef(ref V1);
}

} *)

(*

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION
====