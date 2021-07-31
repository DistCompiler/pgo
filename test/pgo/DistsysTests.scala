package pgo

import org.scalatest.funsuite.AnyFunSuite

class DistsysTests extends AnyFunSuite {
  test("distsys module tests") {
    os.proc("go", "test").call(cwd = os.pwd / "distsys")
  }
}
