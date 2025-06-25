import scala.util.Random

val rng = Random()

(0 until 100).foreach: _ =>
  rng.nextBoolean() match
    case true =>
      println(s"get ${rng.nextPrintableChar()}")
    case false =>
      println(s"put ${rng.nextPrintableChar()} ${rng.nextPrintableChar()}")
