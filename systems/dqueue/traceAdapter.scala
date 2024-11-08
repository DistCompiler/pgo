//> using scala 3

//> using dep com.lihaoyi::os-lib:0.11.3
//> using dep com.lihaoyi::ujson:4.0.2

import scala.util.Using
import scala.collection.mutable

// TODO: get the termination argument right (it's that hyperproperty trick, but I am dumb rn)

val actionRenamings = Map(
  "AConsumer.c" -> "c",
  "AConsumer.c1" -> "c1",
  "AConsumer.c2" -> "c2",
  "AProducer.p" -> "p",
  "AProducer.p1" -> "p1",
  "AProducer.p2" -> "p2"
)

val globalVariableRenamings = Map(
  "AConsumer.proc" -> "processor"
)
val localVariableRenamings = Map(
  "AProducer.requester" -> "requester"
)
val macroProcRenamings = Map(
  "AProducer.net" -> "network",
  "AConsumer.net" -> "network",
  "AProducer.s" -> "stream",
)

enum Var:
  case Global(name: String)
  case Local(name: String)
  case Macro(name: String)

@main
def traceAdapter(): Unit =
  val out = StringBuilder()

  val variables = Seq(
    "network",
    "stream",
    "processor",
    "pc",
    "requester",
  )

  out ++=
    s"""---- MODULE dqueueValidate ----
       |EXTENDS Sequences, Integers, TLC, FiniteSetsExt
       |
       |CONSTANTS
       |  defaultInitValue,
       |  NUM_CONSUMERS,
       |  PRODUCER,
       |  BUFFER_SIZE
       |
       |VARIABLES __clock, ${variables.mkString(", ")}
       |
       |vars == <<__clock, ${variables.mkString(", ")}>>
       |
       |__clock_merge(clk1, clk2) ==
       |  LET wholeDomain == DOMAIN clk1 \\cup DOMAIN clk2
       |      whole(clk) ==
       |        [idx \\in wholeDomain |-> IF idx \\in DOMAIN clk THEN clk[idx] ELSE 0]
       |  IN  [idx \\in wholeDomain |-> Max({whole(clk1)[idx], whole(clk2)[idx]})]
       |
       |__clock_check(self, clock) ==
       |  LET wholeDomain == DOMAIN __clock \\cup DOMAIN clock
       |      whole(clk) ==
       |        [idx \\in wholeDomain |-> IF idx \\in DOMAIN clk THEN clk[idx] ELSE 0]
       |  IN  /\\ whole(__clock)[self] + 1 = whole(clock)[self]
       |      \\* /\\ \\A idx \\in wholeDomain : whole(__clock)[idx] <= whole(clock)[idx]
       |      /\\ __clock' = __clock_merge(__clock, clock)
       |
       |network_read(self, idx, value) ==
       |  /\\ network[idx] # <<>>
       |  /\\ Head(network[idx]) = value
       |  /\\ network' = [network EXCEPT ![idx] = Tail(@)]
       |
       |network_write(self, idx, value) ==
       |  /\\ network' = [network EXCEPT ![idx] = Append(@, value)]
       |
       |stream_read(self, value) ==
       |  /\\ stream' = (stream + 1) % BUFFER_SIZE
       |  /\\ value = stream'
       |
       |dqueue == INSTANCE dqueue
       |
       |Init ==
       |  /\\ dqueue!Init
       |  /\\ __clock = <<>>
       |""".stripMargin

  val validateLabelCounters = mutable.HashMap[String, Int]()
  val validateLabels = mutable.ListBuffer[String]()

  def mkFreshValidateLabel(label: String)(lines: IterableOnce[String]): Unit =
    val counter = validateLabelCounters.getOrElseUpdate(label, 0)
    validateLabelCounters(label) = counter + 1
    val freshLabel = s"validate_${label}_$counter"
    validateLabels += freshLabel
    out ++= s"\n\n$freshLabel =="
    lines.iterator.foreach: line =>
      out ++= s"\n  /\\ $line"

  os.read.lines
    .stream(os.pwd / "dqueue_trace.txt")
    .foreach: line =>
      val js = ujson.read(line)
      val archetypeName = js("archetypeName").str
      val self = js("self").str
      var labelName = "!!!"
      val variablesUnchanged = variables.to(mutable.SortedSet)
      def markChanged(name: String): Unit =
        variablesUnchanged -= name
      val lines = mutable.ListBuffer[String]()
      js("csElements").arr.foreach: csElem =>
        val tag = csElem("tag").str
        if csElem("name")("name").str == ".pc"
        then
          val mpcalLabelName =
            csElem("value").str.stripPrefix("\"").stripSuffix("\"")
          tag match
            case "read" =>
              assert(labelName == "!!!")
              labelName = actionRenamings(mpcalLabelName)
              lines += s"pc[$self] = \"$labelName\""
            case "write" =>
              markChanged("pc")
              lines += s"pc' = [pc EXCEPT ![$self] = \"${actionRenamings(mpcalLabelName)}\"]"
        else
          val mpcalVariableName =
            s"$archetypeName.${csElem("name")("name").str}"
          val value = csElem("value").str

          val resolvedNameOpt = globalVariableRenamings
            .get(mpcalVariableName)
            .map(Var.Global(_))
            .orElse:
              localVariableRenamings
                .get(mpcalVariableName)
                .map(Var.Local(_))
            .orElse:
              macroProcRenamings
                .get(mpcalVariableName)
                .map(Var.Macro(_))

          assert(resolvedNameOpt.nonEmpty, s"couldn't resolve $mpcalVariableName")
          
          val indices = csElem("indices").arr.map(_.str)
          val indicesStr =
            if indices.nonEmpty
            then s"[${indices.mkString(", ")}]"
            else ""
          val indicesStrSuffix = indices
            .iterator
            .map(idx => s", $idx")
            .mkString

          (tag, resolvedNameOpt.get) match
            case ("read", Var.Global(resolvedName)) =>
              lines += s"$resolvedName$indicesStr = $value"
            case ("write", Var.Global(resolvedName)) =>
              if indices.nonEmpty
              then
                lines += s"$resolvedName' = [$resolvedName EXCEPT ![${indices.mkString(", ")}] = $value]"
              else
                lines += s"$resolvedName' = $value"
              markChanged(resolvedName)
            case ("read", Var.Macro(macroName)) =>
              lines += s"${macroName}_read($self$indicesStrSuffix, $value)"
              markChanged(macroName)
            case ("write", Var.Macro(macroName)) =>
              lines += s"${macroName}_write($self$indicesStrSuffix, $value)"
              markChanged(macroName)
            case ("read", Var.Local(name)) =>
              lines += s"$name[$self]$indicesStr = $value"
            case ("write", Var.Local(name)) =>
              if indices.nonEmpty
              then
                // hack? somehow indices has self in it for writes...
                lines += s"$name' = [$name EXCEPT ![$self][${indices.mkString(", ")}] = $value]"
              else
                lines += s"$name' = [$name EXCEPT ![$self] = $value]"
              markChanged(name)
            case _ => ???

      val clock =
        js("clock").arr
          .iterator
          .map(_.arr)
          .map:
            case mutable.ArrayBuffer(idx, value) =>
              s"${idx(1).str} :> ${value.num.toInt}"
            case _ => ???
          .mkString(" @@ ")

      lines += s"__clock_check($self, $clock)"

      if variablesUnchanged.nonEmpty
      then lines += s"UNCHANGED <<${variablesUnchanged.mkString(", ")}>>"

      mkFreshValidateLabel(labelName)(lines)

  out ++=
    s"""
       |
       |Next == ${validateLabels.iterator.map(lbl => s"\n  \\/ $lbl").mkString}
       |
       |RECURSIVE ClockSum(_)
       |
       |ClockSum(clock) ==
       |  IF   clock = <<>>
       |  THEN 0
       |  ELSE LET idx == CHOOSE i \\in DOMAIN clock : TRUE
       |       IN  clock[idx] + ClockSum([i \\in DOMAIN clock \\ {idx} |-> clock[i]])
       |
       |LoopAtEnd ==
       |  /\\ ClockSum(__clock) = ${validateLabels.size}
       |  /\\ UNCHANGED vars
       |
       |Spec ==
       |  /\\ Init
       |  /\\ [][Next \\/ LoopAtEnd]_vars
       |
       |IsRefinement == [][dqueue!Next]_vars
       |
       |ClockSumLooksRight ==
       |  ClockSum(__clock) \\in Int
       |
       |DiameterCheck ==
       |  LET d == TLCGet("stats").diameter
       |  IN IF d - 1 = ${validateLabels.size}
       |     THEN TRUE
       |     ELSE Print(<<"diameter was actually", d>>, FALSE)
       |
       |PseudoTermination ==
       |  TLCGet("stats").diameter - 1 = ${validateLabels.size}
       |  => TLCSet("exit", TRUE)
       |
       |====""".stripMargin

  os.write.over(os.pwd / "dqueueValidate.tla", out.result())
  os.write.over(
    os.pwd / "dqueueValidate.cfg",
    s"""SPECIFICATION Spec
       |
       |PROPERTY IsRefinement
       |INVARIANT ClockSumLooksRight
       |
       |CONSTANT defaultInitValue = defaultInitValue
       |CONSTANT CONSUMER = 1
       |CONSTANT PRODUCER = 0
       |CONSTANT NUM_CONSUMERS = 1
       |CONSTANT BUFFER_SIZE = 100
       |
       |\\* SEFM version
       |POSTCONDITION DiameterCheck
       |CONSTRAINT PseudoTermination
       |
       |CHECK_DEADLOCK FALSE
       |
       |""".stripMargin)
