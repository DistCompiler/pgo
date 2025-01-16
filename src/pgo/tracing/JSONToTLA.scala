package pgo.tracing

import scala.collection.mutable
import scala.util.matching.Regex
import scala.collection.immutable.LazyList.cons
import scala.runtime.stdLibPatches.language.deprecated.symbolLiterals
import ujson.Num
import pgo.util.TLAExprInterpreter
import pgo.util.TLAExprInterpreter.*

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
    val modelValues: Set[String]
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
      modelValues = modelValues
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
      modelValues = modelValues
    )

  def mpcalLocal(mpcalName: String, tlaName: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns =
        mpcalVariableDefns.updated(mpcalName, MPCalVariable.Local(tlaName)),
      modelVariableDefns = modelVariableDefns + tlaName,
      constantDefns = constantDefns,
      modelValues = modelValues
    )

  def mpcalGlobal(mpcalName: String, tlaName: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns =
        mpcalVariableDefns.updated(mpcalName, MPCalVariable.Global(tlaName)),
      modelVariableDefns = modelVariableDefns + tlaName,
      constantDefns = constantDefns,
      modelValues = modelValues
    )

  def mpcalMacro(mpcalName: String, tlaOperatorPrefix: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns = mpcalVariableDefns
        .updated(mpcalName, MPCalVariable.Mapping(tlaOperatorPrefix)),
      modelVariableDefns = modelVariableDefns,
      constantDefns = constantDefns,
      modelValues = modelValues
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
      modelValues = modelValues
    )

  def modelValue(name: String): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns = mpcalVariableDefns,
      modelVariableDefns = modelVariableDefns,
      constantDefns = constantDefns,
      modelValues = modelValues + name
    )

  private def getLabelNameFromValue(value: String): String =
    val mpcalLabelName = value.stripPrefix("\"").stripSuffix("\"")
    actionRenamings.get(mpcalLabelName) match
      case Some(name) => name
      case None =>
        val splits = mpcalLabelName.split(Regex.quote("."))
        assert(splits.size >= 2, s"couldn't auto split $mpcalLabelName")
        splits.last

  private def tlaStringToJSON(str: String): ujson.Value =
    val value = TLAValue.parseFromString(str)
    def impl(value: TLAValue): ujson.Value =
      value match
        case TLAValueModel(name)   => ???
        case TLAValueBool(value)   => ujson.Bool(value)
        case TLAValueNumber(value) => ujson.Num(value)
        case TLAValueString(value) => ujson.Str(value)
        case TLAValueSet(value)    => ???
        case TLAValueTuple(value) =>
          value.view.map(impl)
        case TLAValueFunction(value) =>
          value.view.map: (key, value) =>
            impl(key).str -> impl(value)
        case TLAValueLambda(fn) => ???

    impl(value)

  def generate(traceFiles: List[os.Path]): Unit =
    val out = StringBuilder()
    val variables = (modelVariableDefns + "pc" + "__clock").toSeq.sorted
    val variablesWithoutClock = variables.filter(_ != "__clock")

    out ++=
      s"""---- MODULE ${modelName}Validate ----
        |EXTENDS ${tlaExtends.mkString(", ")}
        |
        |__all_strings == IODeserialize("${modelName}AllStrings.bin", FALSE)
        |
        |CONSTANT ${modelValues.mkString(", ")}
        |${constantDefns.toSeq.view.sorted
          .map((name, value) => s"\n$name == $value")
          .mkString}
        |
        |VARIABLES ${variables.mkString(", ")}
        |
        |vars == <<${variables.mkString(", ")}>>
        |
        |__clock_at(__clk, __idx) ==
        |  IF __idx \\in DOMAIN __clk
        |  THEN __clk[__idx]
        |  ELSE 0
        |
        |__clock_check(self, __clk) ==
        |  /\\ \\A __i \\in (DOMAIN __clock \\cup DOMAIN __clk) :
        |      __clock_at(__clock, __i) <= __clock_at(__clk, __i)
        |  /\\ \\E __i \\in (DOMAIN __clock \\cup DOMAIN __clk) :
        |      __clock_at(__clock, __i) < __clock_at(__clk, __i)
        |  /\\ __clock' = [__i \\in DOMAIN __clock \\cup {self} |->
        |        IF __i = self
        |        THEN __clock_at(__clock, __i) + 1
        |        ELSE __clock_at(__clock, __i)]
        |
        |__records == IODeserialize("${modelName}ValidateData.bin", FALSE)
        |
        |__state_get == [${variablesWithoutClock.view
          .filter(_ != "__clock")
          .map(v => s"\n  $v |-> $v")
          .mkString(", ")}]
        |
        |__state_set(__state_prime) ==${variablesWithoutClock.view
          .map(v => s"\n  /\\ $v' = __state_prime.$v")
          .mkString}
        |
        |__instance == INSTANCE $modelName
        |
        |__defns == INSTANCE ${modelName}ValidateDefns
        |
        |Init ==
        |  /\\ __instance!Init
        |  /\\ __clock = <<>>""".stripMargin

    val labelCounters = mutable.HashMap[String, Int]()
    val criticalSectionDebupSet = mutable.HashSet[String]()
    val selfKeys = mutable.HashSet[String]()

    val records =
      mutable.HashMap[String, mutable.ArrayBuffer[Map[String, String]]]()

    traceFiles.foreach: traceFile =>
      println(s"reading $traceFile...")
      os.read.lines
        .stream(traceFile)
        .foreach: line =>
          val js = ujson.read(line)
          val archetypeName = js("archetypeName").str
          val selfValue = js("self").str
          val selfRecordsKey = selfValue
          selfKeys += selfRecordsKey

          val elems = mutable.ArrayBuffer.empty[String]

          val csElements = js("csElements").arr
          assert(csElements.head("name")("name").str == ".pc")
          val labelName = getLabelNameFromValue(csElements.head("value").str)

          val localOut = StringBuilder()

          var indent = 0
          var alreadyInPosition = false

          def addLine(str: String): Unit =
            if !alreadyInPosition
            then
              localOut += '\n'
              localOut ++= (0 until indent).view.map(_ => ' ')
              localOut ++= str
            else
              localOut ++= str
              alreadyInPosition = false

          val suffix = StringBuilder()

          val fullLabelName = s"${archetypeName}_$labelName"
          val thisLabelIdx = labelCounters.getOrElse(fullLabelName, 0)

          indent += 2
          var stateCounter = 0
          def stateName: String = s"__state$stateCounter"
          addLine(
            "(__clock_at(__clock, self) + 1) \\in DOMAIN __records[self] /\\"
          )
          addLine(s"LET $stateName == __state_get")
          addLine(
            s"    __record == __records[self][__clock_at(__clock, self) + 1]"
          )
          addLine(s"    __elems == __record.elems")
          addLine(s"IN  ")
          alreadyInPosition = true
          indent += 4
          addLine(s"/\\ pc[self] = \"$labelName\"")

          csElements.view.tail.zipWithIndex.foreach: (csElem, csIdx) =>
            val elemRec = mutable.HashMap.empty[String, String]
            val elem = s"__elems[${csIdx + 1}]"
            val tag = csElem("tag").str
            val mpcalVariableName =
              csElem("name")("name").str match
                case ".pc" => ".pc"
                case name  => s"$archetypeName.$name"
            val value =
              mpcalVariableName match
                case ".pc" =>
                  s"\"${getLabelNameFromValue(csElem("value").str)}\""
                case _ => s"$elem.value"

            if mpcalVariableName != ".pc"
            then elemRec("value") = csElem("value").str

            elemRec("indices") =
              csElem("indices").arr.view.map(_.str).mkString("<<", ", ", ">>")
            val indicesList = csElem("indices").arr.indices.view
              .map(idx => s"$elem.indices[${idx + 1}]")
              .mkString(", ")
            val indicesPath =
              if indicesList.nonEmpty
              then s"[$indicesList]"
              else ""
            val indicesArgs =
              if indicesList.nonEmpty
              then s", $indicesList"
              else ""

            elems += elemRec.view
              .map((key, value) => s"$key |-> $value")
              .mkString("[", ", ", "]")

            tag match
              case "read" =>
                mpcalVariableDefns(mpcalVariableName) match
                  case MPCalVariable.Local(tlaVar) =>
                    addLine(
                      s"/\\ $stateName.$tlaVar[self]$indicesPath = $value"
                    )
                  case MPCalVariable.Global(tlaVar) =>
                    addLine(s"/\\ $stateName.$tlaVar$indicesPath = $value")
                  case MPCalVariable.Mapping(tlaOperatorPrefix) =>
                    val prevState = stateName
                    stateCounter += 1
                    addLine(
                      s"/\\ __defns!${tlaOperatorPrefix}_read($prevState, self$indicesArgs, $value, LAMBDA $stateName:"
                    )
                    indent += 5
                    suffix += ')'
              case "write" =>
                mpcalVariableDefns(mpcalVariableName) match
                  case v @ (MPCalVariable.Local(_) | MPCalVariable.Global(_)) =>
                    val (tlaVar, pathStr) = v match
                      case MPCalVariable.Global(tlaVar) =>
                        (tlaVar, indicesPath)
                      case MPCalVariable.Local(tlaVar) =>
                        (tlaVar, s"[self]$indicesPath")

                    val prevState = stateName
                    stateCounter += 1
                    addLine(
                      s"/\\ LET $stateName == [$prevState EXCEPT !.$tlaVar$pathStr = $value]"
                    )
                    addLine(s"   IN  ")
                    indent += 7
                    alreadyInPosition = true
                  case MPCalVariable.Mapping(tlaOperatorPrefix) =>
                    val prevState = stateName
                    stateCounter += 1
                    addLine(
                      s"/\\ __defns!${tlaOperatorPrefix}_write($prevState, self$indicesArgs, $value, LAMBDA $stateName:"
                    )
                    indent += 5
                    suffix += ')'
              case _ => ???

          addLine(s"/\\ __clock_check(self, __record.clock)")
          addLine(s"/\\ __state_set($stateName)")
          localOut ++= suffix

          val record = Map(
            "self" -> selfValue,
            "clock" -> js("clock").arr.view
              .map:
                case ujson.Arr(
                      mutable.ArrayBuffer(
                        ujson.Arr(mutable.ArrayBuffer(_, self)),
                        idx
                      )
                    ) =>
                  s"${self.str} :> $idx"
                case _ => ???
              .mkString("(", " @@ ", ")"),
            "elems" -> elems.mkString("<<", ", ", ">>")
          )
          records.getOrElseUpdate(
            selfRecordsKey,
            mutable.ArrayBuffer.empty
          ) += record

          val csStr = localOut.result()
          if !criticalSectionDebupSet(csStr)
          then
            labelCounters(fullLabelName) =
              labelCounters.getOrElse(fullLabelName, 0) + 1
            out += '\n'
            out += '\n'
            out ++= s"${fullLabelName}_$thisLabelIdx(self) =="
            out ++= csStr
            criticalSectionDebupSet += csStr

    val allValidateLabels =
      labelCounters.toArray.sorted.view
        .flatMap: (name, max) =>
          (0 until max).view
            .map(idx => s"${name}_$idx")

    out ++= s"""
              |Next ==
              |  \\E self \\in {${selfKeys.toSeq.sorted.mkString(
                ", "
              )}} :${allValidateLabels
                .map(name => s"\n    \\/ $name(self)")
                .mkString}
              |
              |RECURSIVE ClockSum(_)
              |
              |ClockSum(__clk) ==
              |  IF   __clk = <<>>
              |  THEN 0
              |  ELSE LET __idx == CHOOSE i \\in DOMAIN __clk : TRUE
              |       IN  __clk[__idx] + ClockSum([__i \\in DOMAIN __clk \\ {__idx} |-> __clk[__i]])
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

    os.write.over(
      destDir / s"${modelName}Validate.tla",
      out.result(),
      createFolders = true
    )

    os.write.over(
      destDir / s"${modelName}Validate.cfg",
      s"""SPECIFICATION Spec
        |
        |PROPERTY IsRefinement
        |
        |${modelValues.view
          .map(name => s"CONSTANT $name = $name")
          .mkString("\n")}
        |""".stripMargin
    )

    val dataValue =
      TLAValueFunction:
        records.view
          .map: (self, records) =>
            TLAValue.parseFromString(self) -> TLAValueTuple:
              records.view
                .map: rec =>
                  TLAValueFunction:
                    rec.view
                      .map: (k, v) =>
                        TLAValueString(k) -> TLAValue.parseFromString(v)
                      .toMap
                .toVector
          .toMap

    os.write.over(
      destDir / s"${modelName}ValidateData.bin",
      dataValue.asTLCBinFmt
    )

    val allStringsValue =
      val stringsAcc = mutable.HashSet.empty[String]
      def impl(v: TLAValue): Unit =
        v match
          case TLAValueModel(name)   =>
          case TLAValueBool(value)   =>
          case TLAValueNumber(value) =>
          case TLAValueString(value) =>
            stringsAcc += value
          case TLAValueSet(value) =>
            value.foreach(impl)
          case TLAValueTuple(value) =>
            value.foreach(impl)
          case TLAValueFunction(value) =>
            value.foreach: (k, v) =>
              impl(k)
              impl(v)
          case TLAValueLambda(fn) =>

      impl(dataValue)
      TLAValueSet(stringsAcc.iterator.map(TLAValueString.apply).toSet)
    end allStringsValue

    os.write.over(
      destDir / s"${modelName}AllStrings.bin",
      allStringsValue.asTLCBinFmt
    )
  end generate

object JSONToTLA:
  def apply(modelName: String, destDir: os.Path): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      destDir = destDir,
      tlaExtends =
        List("Sequences", "Integers", "TLC", "IOUtils", "FiniteSetsExt"),
      actionRenamings = Map.empty,
      mpcalVariableDefns = Map(".pc" -> MPCalVariable.Local("pc")),
      modelVariableDefns = Set.empty,
      constantDefns = Map.empty,
      modelValues = Set("defaultInitValue")
    )
