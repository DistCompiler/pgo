package pgo.tracing

import scala.collection.mutable
import scala.util.matching.Regex
import scala.collection.immutable.LazyList.cons

enum MPCalVariable:
  case Local(tlaVar: String)
  case Global(tlaVar: String)
  case Mapping(tlaOperatorPrefix: String)

final class JSONToTLA private (
  val modelName: String,
  val destDir: os.Path,
  val tlaExtends: List[String],
  val actionRenamings: Map[String, String],
  val mpcalVariableDefns: Map[String, MPCalVariable],
  val modelVariableDefns: Set[String],
  val constantDefns: Map[String, String],
):
  def renameLabel(mpcalName: String, labelName: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings.updated(mpcalName, labelName),
      mpcalVariableDefns = mpcalVariableDefns,
      modelVariableDefns = modelVariableDefns,
      constantDefns = constantDefns,
    )

  def modelVariable(name: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns = mpcalVariableDefns,
      modelVariableDefns = modelVariableDefns + name,
      constantDefns = constantDefns,
    )

  def mpcalLocal(mpcalName: String, tlaName: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns = mpcalVariableDefns.updated(mpcalName, MPCalVariable.Local(tlaName)),
      modelVariableDefns = modelVariableDefns + tlaName,
      constantDefns = constantDefns,
    )

  def mpcalGlobal(mpcalName: String, tlaName: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns = mpcalVariableDefns.updated(mpcalName, MPCalVariable.Global(tlaName)),
      modelVariableDefns = modelVariableDefns + tlaName,
      constantDefns = constantDefns,
    )

  def mpcalMacro(mpcalName: String, tlaOperatorPrefix: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns = mpcalVariableDefns.updated(mpcalName, MPCalVariable.Mapping(tlaOperatorPrefix)),
      modelVariableDefns = modelVariableDefns,
      constantDefns = constantDefns,
    )

  def tlaConstant(name: String, value: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns = mpcalVariableDefns,
      modelVariableDefns = modelVariableDefns,
      constantDefns = constantDefns.updated(name, value),
    )

  private def getLabelNameFromValue(value: String): String =
    val mpcalLabelName = value.stripPrefix("\"").stripSuffix("\"")
    actionRenamings.get(mpcalLabelName) match
      case Some(name) => name
      case None =>
        val splits = mpcalLabelName.split(Regex.quote("."))
        assert(splits.size >= 2, s"couldn't auto split $mpcalLabelName")
        splits.last

  def generate(traceFile: os.Path): Unit =
    val out = StringBuilder()
    val variables = (modelVariableDefns + "pc" + "__clock").toSeq.sorted
    val variablesWithoutClock = variables.filter(_ != "__clock")

    out ++=
      s"""---- MODULE ${modelName}Validate ----
        |EXTENDS ${tlaExtends.mkString(", ")}
        |
        |CONSTANT defaultInitValue${
          constantDefns
            .toSeq
            .view
            .sorted
            .map((name, value) => s"\n$name == $value")
            .mkString
        }
        |
        |VARIABLES ${variables.mkString(", ")}
        |
        |vars == <<${variables.mkString(", ")}>>
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
        |      /\\ __clock' = __clock_merge(__clock, clock)
        |
        |__state_get == [${variablesWithoutClock.view.filter(_ != "__clock").map(v => s"\n  $v |-> $v").mkString(", ")}]
        |
        |__state_set(__state_prime) ==${variablesWithoutClock.view.map(v => s"\n  /\\ $v' = __state_prime.$v").mkString}
        |
        |__instance == INSTANCE $modelName
        |
        |__defns == INSTANCE ${modelName}ValidateDefns
        |
        |Init ==
        |  /\\ __instance!Init
        |  /\\ __clock = <<>>""".stripMargin

    val labelCounters = mutable.HashMap[String, Int]()

    os.read.lines
      .stream(traceFile)
      .foreach: line =>
        val js = ujson.read(line)
        val archetypeName = js("archetypeName").str
        val self = js("self").str

        val csElements = js("csElements").arr
        assert(csElements.head("name")("name").str == ".pc")
        val labelName = getLabelNameFromValue(csElements.head("value").str)

        val clockValueSelf =
          js("clock").arr
            .view
            .find(_(0)(1).str == self)
            .map(_(1).num.toInt)
            .get
        val clockValue =
          js("clock").arr
            .view
            .map(_.arr)
            .collect:
              case mutable.ArrayBuffer(idx, value) =>
                s"${idx(1).str} :> ${value.num.toInt}"
            .mkString(" @@ ")

        var indent = 0
        var alreadyInPosition = false

        def addLine(str: String): Unit =
          if !alreadyInPosition
          then
            out += '\n'
            out ++= (0 until indent).view.map(_ => ' ')
            out ++= str
          else
            out ++= str
            alreadyInPosition = false

        val suffix = StringBuilder()

        addLine("")
        locally:
          val fullLabelName = s"${archetypeName}_$labelName"
          val labelIdx = labelCounters.getOrElse(fullLabelName, 0)
          labelCounters(fullLabelName) = labelIdx + 1
          addLine(s"${fullLabelName}_$labelIdx ==")

        indent += 2
        if clockValueSelf == 1
        then addLine(s"/\\ IF $self \\in DOMAIN __clock THEN __clock[$self] = 0 ELSE TRUE")
        else addLine(s"/\\ $self \\in DOMAIN __clock /\\ __clock[$self] = ${clockValueSelf - 1}")
        addLine(s"/\\ pc[$self] = \"$labelName\"")
        var stateCounter = 0
        def stateName: String = s"__state$stateCounter"
        addLine(s"/\\ LET $stateName == __state_get")
        addLine(s"   IN  ")
        alreadyInPosition = true
        indent += 7

        csElements.view.tail.foreach: csElem =>
          val tag = csElem("tag").str
          val mpcalVariableName =
            csElem("name")("name").str match
              case ".pc" => ".pc"
              case name => s"$archetypeName.$name"
          val value =
            mpcalVariableName match
              case ".pc" => s"\"${getLabelNameFromValue(csElem("value").str)}\""
              case _ => csElem("value").str

          val indicesList = csElem("indices").arr.view.map(_.str).mkString(", ")
          val indicesPath =
            if indicesList.nonEmpty
            then s"[$indicesList]"
            else ""
          val indicesArgs =
            if indicesList.nonEmpty
            then s", $indicesList"
            else ""

          tag match
            case "read" =>
              mpcalVariableDefns(mpcalVariableName) match
                case MPCalVariable.Local(tlaVar) =>
                  addLine(s"/\\ $stateName.$tlaVar[$self]$indicesPath = $value")
                case MPCalVariable.Global(tlaVar) =>
                  addLine(s"/\\ $stateName.$tlaVar$indicesPath = $value")
                case MPCalVariable.Mapping(tlaOperatorPrefix) =>
                  val prevState = stateName
                  stateCounter += 1
                  addLine(s"/\\ __defns!${tlaOperatorPrefix}_read($prevState, $self$indicesArgs, $value, LAMBDA $stateName:")
                  indent += 5
                  suffix += ')'
            case "write" =>
              mpcalVariableDefns(mpcalVariableName) match
                case v @ (MPCalVariable.Local(_) | MPCalVariable.Global(_)) =>
                  val (tlaVar, pathStr) = v match
                    case MPCalVariable.Global(tlaVar) =>
                      (tlaVar, indicesPath)
                    case MPCalVariable.Local(tlaVar) =>
                      (tlaVar, s"[$self]$indicesPath")

                  val prevState = stateName
                  stateCounter += 1
                  addLine(s"/\\ LET $stateName == [$prevState EXCEPT !.$tlaVar$pathStr = $value]")
                  addLine(s"   IN  ")
                  indent += 7
                  alreadyInPosition = true
                case MPCalVariable.Mapping(tlaOperatorPrefix) =>
                  val prevState = stateName
                  stateCounter += 1
                  addLine(s"/\\ __defns!${tlaOperatorPrefix}_write($prevState, $self$indicesArgs, $value, LAMBDA $stateName:")
                  indent += 5
                  suffix += ')'
            case _ => ???
        
        addLine(s"/\\ __clock_check($self, $clockValue)")
        addLine(s"/\\ __state_set($stateName)")
        out ++= suffix

    val allValidateLabels =
      labelCounters
        .toArray
        .sorted
        .view
        .flatMap: (name, max) =>
          (0 until max)
            .view
            .map(idx => s"${name}_$idx")

    out ++= s"""
              |Next ==${allValidateLabels.map(name => s"\n  \\/ $name").mkString}
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
              |  /\\ ClockSum(__clock) = ${allValidateLabels.size}
              |  /\\ UNCHANGED vars
              |
              |Spec ==
              |  /\\ Init
              |  /\\ [][Next \\/ LoopAtEnd]_vars
              |
              |IsRefinement == [][__instance!Next]_vars
              |
              |====
              |""".stripMargin

    os.write.over(destDir / s"${modelName}Validate.tla", out.result(), createFolders = true)

    os.write.over(
      destDir / s"${modelName}Validate.cfg",
      s"""SPECIFICATION Spec
        |
        |PROPERTY IsRefinement
        |
        |CONSTANT defaultInitValue = defaultInitValue
        |""".stripMargin)
  end generate

object JSONToTLA:
  def apply(modelName: String, destDir: os.Path): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = List("Sequences", "Integers", "TLC", "FiniteSetsExt"),
      actionRenamings = Map.empty,
      mpcalVariableDefns = Map(".pc" -> MPCalVariable.Local("pc")),
      modelVariableDefns = Set.empty,
      constantDefns = Map.empty,
    )
