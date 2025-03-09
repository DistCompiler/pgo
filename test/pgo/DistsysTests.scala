package pgo

class DistsysTests extends munit.FunSuite {
  test("distsys module tests") {
    os.proc("go", "test", "./...")
      .call(
        cwd = os.pwd / "distsys",
        stdout = os.InheritRaw,
        stderr = os.InheritRaw,
      )
  }
}
