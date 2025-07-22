package pgo.tracing

import scala.collection.mutable
import scala.util.matching.Regex
import pgo.util.TLAExprInterpreter
import pgo.util.TLAExprInterpreter.*
import java.time.Instant
import scala.util.chaining.given
import scala.collection.immutable.ArraySeq
import scala.collection.Searching
import java.time.temporal.ChronoUnit

enum MPCalVariable:
  case Local(tlaVar: String)
  case Global(tlaVar: String)
  case Mapping(tlaOperatorPrefix: String)

final class JSONToTLA private (
    val modelName: String,
    val allPaths: Boolean,
    val destDir: os.Path,
    val tlaExtends: Set[String],
    val actionRenamings: Map[String, String],
    val mpcalVariableDefns: Map[String, MPCalVariable],
    val modelVariableDefns: Set[String],
    val constantDefns: Set[String],
    val modelValues: Set[String],
    val additionalDefns: List[String],
    val progressInv: Boolean,
    val physicalClocks: Boolean,
):
  def copy(
      modelName: String = modelName,
      allPaths: Boolean = allPaths,
      destDir: os.Path = destDir,
      tlaExtends: Set[String] = tlaExtends,
      actionRenamings: Map[String, String] = actionRenamings,
      mpcalVariableDefns: Map[String, MPCalVariable] = mpcalVariableDefns,
      modelVariableDefns: Set[String] = modelVariableDefns,
      constantDefns: Set[String] = constantDefns,
      modelValues: Set[String] = modelValues,
      additionalDefns: List[String] = additionalDefns,
      progressInv: Boolean = progressInv,
      physicalClocks: Boolean = physicalClocks,
  ): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      allPaths = allPaths,
      destDir = destDir,
      tlaExtends = tlaExtends,
      actionRenamings = actionRenamings,
      mpcalVariableDefns = mpcalVariableDefns,
      modelVariableDefns = modelVariableDefns,
      constantDefns = constantDefns,
      modelValues = modelValues,
      additionalDefns = additionalDefns,
      progressInv = progressInv,
      physicalClocks = physicalClocks,
    )

  def withTLAExtends(name: String): JSONToTLA =
    copy(tlaExtends = tlaExtends + name)

  def renameLabel(mpcalName: String, labelName: String): JSONToTLA =
    copy(actionRenamings = actionRenamings.updated(modelName, labelName))

  def modelVariable(name: String): JSONToTLA =
    copy(modelVariableDefns = modelVariableDefns + name)

  def mpcalLocal(mpcalName: String, tlaName: String): JSONToTLA =
    copy(
      mpcalVariableDefns =
        mpcalVariableDefns.updated(mpcalName, MPCalVariable.Local(tlaName)),
      modelVariableDefns = modelVariableDefns + tlaName,
    )

  def mpcalGlobal(mpcalName: String, tlaName: String): JSONToTLA =
    copy(
      mpcalVariableDefns =
        mpcalVariableDefns.updated(mpcalName, MPCalVariable.Global(tlaName)),
      modelVariableDefns = modelVariableDefns + tlaName,
    )

  def mpcalMacro(mpcalName: String, tlaOperatorPrefix: String): JSONToTLA =
    copy(mpcalVariableDefns =
      mpcalVariableDefns.updated(
        mpcalName,
        MPCalVariable.Mapping(tlaOperatorPrefix),
      ),
    )

  def tlaConstant(name: String): JSONToTLA =
    copy(constantDefns = constantDefns + name)

  def modelValue(name: String): JSONToTLA =
    copy(modelValues = modelValues + name)

  def withAdditionalDefns(defns: List[String]): JSONToTLA =
    copy(additionalDefns = additionalDefns ::: defns)

  def withAllPaths(allPaths: Boolean): JSONToTLA =
    copy(allPaths = allPaths)

  def withProgressInv(progressInv: Boolean): JSONToTLA =
    copy(progressInv = progressInv)

  def withPhysicalClocks(physicalClocks: Boolean): JSONToTLA =
    copy(physicalClocks = physicalClocks)

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
    val variables =
      (modelVariableDefns + "pc" + "__clock" + "__action").toSeq.sorted
    val userVariables = variables.filterNot(Set("__clock", "__action"))

    out ++=
      s"""---- MODULE ${modelName}Validate ----
         |EXTENDS ${tlaExtends.mkString(", ")}
         |
         |\\* FIXME: caching!
         |\\* __all_strings == TLCCache(IODeserialize("${modelName}AllStrings.bin", FALSE), {"allStrings"})
         |__all_strings == IODeserialize("${modelName}AllStrings.bin", FALSE)
         |
         |CONSTANT ${(modelValues ++ constantDefns).mkString(", ")}
         |
         |\\* Additional defns start
         |${additionalDefns.mkString("\n")}
         |\\* Additional defns end
         |
         |VARIABLES ${variables.mkString(", ")}
         |
         |vars == <<${variables.mkString(", ")}>>
         |__user_vars == <<${userVariables.mkString(", ")}>>
         |
         |__clock_at(__clk, __idx) ==
         |  IF __idx \\in DOMAIN __clk
         |  THEN __clk[__idx]
         |  ELSE 0
         |
         |__time_lt_pair(__pair1, __pair2) ==
         |  \\/ __pair1[1] < __pair2[1]
         |  \\/ /\\ __pair1[1] = __pair2[1]
         |      /\\ __pair1[2] < __pair2[2]
         |
         |__time_lt_rec(__rec1, __rec2) ==
         |  __time_lt_pair(__rec1.endTime, __rec2.startTime)
         |
         |\\* FIXME: caching!
         |\\* __records == TLCCache(IODeserialize("${modelName}ValidateData.bin", FALSE), {"validateData"})
         |__records == IODeserialize("${modelName}ValidateData.bin", FALSE)
         |
         |__clock_check(self, __commit(_)) ==
         |  LET __idx == __clock_at(__clock, self) + 1
         |      __updated_clock == (self :> __idx) @@ __clock \\* this way round!
         |      __next_clock == __records[self][__idx].clock
         |  IN  /\\ __idx \\in DOMAIN __records[self]
         |      /\\ __updated_clock[self] = __next_clock[self]
         |      /\\ \\A __i \\in DOMAIN __next_clock :
         |           __next_clock[__i] <= __clock_at(__updated_clock, __i)
         |      /\\ __commit(__updated_clock)
         |
         |__state_get == [${userVariables.view
          .filter(_ != "__clock")
          .map(v => s"\n  $v |-> $v")
          .mkString(", ")}]
         |
         |__state_set(__state_prime) ==${userVariables.view
          .map(v => s"\n  /\\ $v' = __state_prime.$v")
          .mkString}
         |
         |__instance == INSTANCE $modelName
         |""".stripMargin

    val labelCounters = mutable.HashMap[String, Int]()
    val criticalSectionDebupSet = mutable.HashSet[String]()
    val selfKeys = mutable.HashSet[String]()

    final case class Elem(
        name: String,
        oldValueOpt: Option[TLAValue],
        value: TLAValue,
        stateName: String,
        indices: IndexedSeq[TLAValue],
        tag: String,
    ):
      def toTLAValue: TLAValue =
        TLAValueFunction:
          Map[TLAValue, TLAValue](
            TLAValueString("name") -> TLAValueString(name),
            TLAValueString("value") -> value,
            TLAValueString("stateName") -> TLAValueString(stateName),
            TLAValueString("indices") -> TLAValueTuple(indices.toVector),
            TLAValueString("tag") -> TLAValueString(tag),
          )
            .pipe: map =>
              oldValueOpt match
                case None => map
                case Some(oldValue) =>
                  map.updated(TLAValueString("oldValue"), oldValue)

    final case class Record(
        pc: String,
        self: TLAValue,
        clock: VClock,
        isAbort: Boolean,
        elems: IndexedSeq[Elem],
        startTime: Instant,
        endTime: Instant,
    ):
      def toTLAValue: TLAValue =
        extension (instant: Instant)
          def toTLAValue: TLAValue =
            TLAValueTuple(
              Vector(
                TLAValueNumber(instant.getEpochSecond().toInt),
                TLAValueNumber(instant.getNano().toInt),
              ),
            )

        TLAValueFunction(
          Map(
            TLAValueString("pc") -> TLAValueString(pc),
            TLAValueString("self") -> self,
            TLAValueString("clock") -> clock.toTLAValue,
            TLAValueString("isAbort") -> TLAValueBool(isAbort),
            TLAValueString("elems") -> TLAValueTuple(
              elems.view.map(_.toTLAValue).toVector,
            ),
            TLAValueString("startTime") -> startTime.toTLAValue,
            TLAValueString("endTime") -> endTime.toTLAValue,
          ),
        )

    val records = mutable.HashMap[TLAValue, mutable.ArrayBuffer[Record]]()

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

          val elems = mutable.ArrayBuffer.empty[Elem]

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
            "(__clock_at(__clock, self) + 1) \\in DOMAIN __records[self] /\\",
          )
          addLine(s"LET $stateName == __state_get")
          addLine(
            s"    __record == __records[self][__clock_at(__clock, self) + 1]",
          )
          addLine(s"    __elems == __record.elems")
          addLine(s"IN  ")
          alreadyInPosition = true
          indent += 4
          addLine(s"/\\ pc[self] = \"$labelName\"")
          addLine(s"/\\ __record.pc = \"$labelName\"")

          addLine(s"/\\ Len(__elems) = ${csElements.size - 1}")

          val isAbort = js.obj.getOrElse("isAbort", ujson.Bool(false)).bool

          if isAbort
          then addLine("/\\ __record.isAbort")
          else addLine("/\\ \\lnot __record.isAbort")

          csElements.view.tail.zipWithIndex.foreach: (csElem, csIdx) =>
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

            val oldValueOpt =
              csElem.obj.get("oldValue") match
                case None => None
                case Some(oldValue) if oldValue.str == "defaultInitValue" =>
                  None // TODO: support this?
                case Some(oldValue) if mpcalVariableName == ".pc" =>
                  None // pc is special
                case Some(oldValue) =>
                  Some(TLAValue.parseFromString(oldValue.str))
            val hasOldValue = oldValueOpt.nonEmpty

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

            elems += Elem(
              name = mpcalVariableName,
              oldValueOpt = oldValueOpt,
              value = TLAValue.parseFromString(csElem("value").str),
              stateName = mpcalVariableDefns(mpcalVariableName) match
                case MPCalVariable.Local(tlaVar)  => tlaVar
                case MPCalVariable.Global(tlaVar) => tlaVar
                case MPCalVariable.Mapping(tlaOperatorPrefix) =>
                  tlaOperatorPrefix,
              indices = csElem("indices").arr.view
                .map(_.str)
                .map(TLAValue.parseFromString)
                .to(ArraySeq),
              tag = tag,
            )

            addLine(s"/\\ $elem.name = \"$mpcalVariableName\"")

            tag match
              case "read" =>
                mpcalVariableDefns(mpcalVariableName) match
                  case MPCalVariable.Local(tlaVar) =>
                    addLine(
                      s"/\\ $stateName.$tlaVar[self]$indicesPath = $value",
                    )
                  case MPCalVariable.Global(tlaVar) =>
                    addLine(s"/\\ $stateName.$tlaVar$indicesPath = $value")
                  case MPCalVariable.Mapping(tlaOperatorPrefix) =>
                    val prevState = stateName
                    stateCounter += 1
                    addLine(
                      s"/\\ ${tlaOperatorPrefix}_read($prevState, self$indicesArgs, $value, LAMBDA $stateName:",
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

                    if hasOldValue
                    then
                      addLine(
                        s"/\\ \"oldValue\" \\in DOMAIN $elem => $stateName.$tlaVar$pathStr = $elem.oldValue",
                      )

                    val prevState = stateName
                    stateCounter += 1
                    addLine(
                      s"/\\ LET $stateName == [$prevState EXCEPT !.$tlaVar$pathStr = $value]",
                    )
                    addLine(s"   IN  ")
                    indent += 7
                    alreadyInPosition = true
                  case MPCalVariable.Mapping(tlaOperatorPrefix) =>
                    val prevState = stateName
                    stateCounter += 1
                    addLine(
                      s"/\\ ${tlaOperatorPrefix}_write($prevState, self$indicesArgs, $value, LAMBDA $stateName:",
                    )
                    indent += 5
                    suffix += ')'
              case _ => ???

          if isAbort
          then addLine("/\\ __commit(__state0, __record)")
          else addLine(s"/\\ __commit($stateName, __record)")
          localOut ++= suffix

          val startTime = Instant.parse(js("startTime").str)
          val endTime = Instant.parse(js("endTime").str)

          val record = Record(
            pc = labelName,
            self = TLAValue.parseFromString(selfValue),
            clock = VClock.fromJSON(js("clock")),
            isAbort = isAbort,
            elems = elems.to(ArraySeq),
            startTime = startTime,
            endTime = endTime,
          )
          records.getOrElseUpdate(
            TLAValue.parseFromString(selfRecordsKey),
            mutable.ArrayBuffer.empty,
          ) += record

          val csStr = localOut.result()
          if !criticalSectionDebupSet(csStr)
          then
            labelCounters(fullLabelName) =
              labelCounters.getOrElse(fullLabelName, 0) + 1
            out += '\n'
            out += '\n'
            out ++= s"${fullLabelName}_$thisLabelIdx(self, __commit(_, _)) =="
            out ++= csStr
            criticalSectionDebupSet += csStr

    val allValidateLabels =
      labelCounters.toArray.sorted.view
        .flatMap: (name, max) =>
          (0 until max).view
            .map(idx => s"${name}_$idx")

    val selfs = selfKeys.toSeq.sorted

    out ++= s"""
               |__self_values == {${selfs.mkString(", ")}}
               |
               |__Init ==
               |  /\\ __instance!Init
               |  /\\ __clock = <<>>
               |  /\\ __action = <<>>
               |
               |__Next_self(self, __commit(_, _)) ==${allValidateLabels
                .map(name => s"\n  \\/ $name(self, __commit)")
                .mkString}
               |
               |__Next ==
               |  \\E self \\in __self_values :
               |    /\\ __clock_check(self, LAMBDA __clk : __clock' = __clk)
               |    /\\ __Next_self(self, LAMBDA __state, __record :
               |        /\\ __action' = __record
               |        /\\ __state_set(__state))
               |
               |__dbg_alias == [
               |  ${variables.map(v => s"$v |-> $v").mkString(",\n  ")},
               |  __dbg_alias |-> [self \\in __self_values |->
               |    IF   __clock_at(__clock, self) + 1 \\in DOMAIN __records[self]
               |    THEN LET __rec == __records[self][__clock_at(__clock, self) + 1]
               |         IN  __rec @@ [
               |           depends_on |-> { __i \\in __self_values :
               |             /\\ __i # self
               |             /\\ __clock_at(__rec.clock, __i) > __clock_at(__clock, __i)
               |           }
               |         ]
               |    ELSE <<>>
               |  ]
               |]
               |
               |__LoopAtEnd ==
               |  /\\ \\A self \\in __self_values :
               |    __clock_at(__clock, self) = Len(__records[self])
               |  /\\ UNCHANGED vars
               |
               |__TerminateAtEnd ==
               |  [][__LoopAtEnd => TLCSet("exit", TRUE)]_vars
               |
               |__Spec ==
               |  /\\ __Init
               |  /\\ [][__Next \\/ __LoopAtEnd]_vars
               |
               |__Stuttering ==
               |  /\\ __clock' # __clock
               |  /\\ UNCHANGED __user_vars
               |
               |__IsRefinement == [][__instance!Next \\/ __Stuttering]_vars
               |
               |${selfs
                .map(self =>
                  s"__progress_inv_$self ==\n  __clock_check($self, LAMBDA _a : TRUE) => __Next_self($self, LAMBDA _a, _b : TRUE)",
                )
                .mkString("\n\n")}
               |
               |====
               |""".stripMargin

    os.write.over(
      destDir / s"${modelName}Validate.tla",
      out.result(),
      createFolders = true,
    )

    os.write.over(
      destDir / s"${modelName}Validate.cfg",
      s"""SPECIFICATION __Spec
         |
         |PROPERTY __IsRefinement
         |
         |${
          if progressInv then
            selfs.map(self => s"INVARIANT __progress_inv_$self").mkString("\n")
          else ""
        }
         |
         |ALIAS __dbg_alias
         |${if allPaths then "" else "\nPROPERTY __TerminateAtEnd"}
         |
         |${modelValues.view
          .map(name => s"CONSTANT $name = $name")
          .mkString("\n")}
         |""".stripMargin,
    )

    // Patch out torn log tails.
    // If node n1 witnesses and logs an action by node n2,
    // but due to interleaving, the action by n2 was not logged
    // in time for some cutoff (shutting down the system), then
    // we end up with a missing log entry which will fail validation.
    // This isn't the system's fault, so we "hide" that in order to
    // focus on actual issues.
    locally:
      // Run to fixpoint for cases where X depends on ... Y depends on Z (where Z is absent).
      var shouldTryPruning = true
      var pruneCount = 0
      while shouldTryPruning
      do
        shouldTryPruning = false
        records.foreach: (self, seq) =>
          val tornRecordIds = mutable.ListBuffer[TLAValue]()
          val countToPrune = seq.reverseIterator
            .takeWhile: elem =>
              elem.clock.indices.exists: (self, idx) =>
                val result = !records(self).indices.contains(idx - 1)
                if result
                then tornRecordIds += self
                result
            .size

          if countToPrune > 0
          then shouldTryPruning = true

          pruneCount += countToPrune
          seq.reverseIterator
            .take(countToPrune)
            .foreach: rec =>
              println(
                s"pruning torn log from $self due to missing record tails: ${tornRecordIds.distinct.mkString(", ")}",
              )
          seq.dropRightInPlace(countToPrune)
      end while

      if pruneCount > 0
      then println(s"pruned $pruneCount log entries")

    if physicalClocks
    then
      records.keysIterator.foreach: self =>
        var selfIdx = 0
        val simClocks = mutable.ArrayBuffer[VClock]()
        records(self).foreach: record =>
          selfIdx += 1
          val startTime = record.startTime
          val simClockKVs =
            records.keysIterator
              .filter(_ != self)
              .map: key =>
                val endTimes = records(key).view.map(_.endTime)
                // Note: the clock has nanosecond precision, so we can search for 1ns less than our start time to
                //       find the largest end time that is before our start time.
                // Note 2: idx is 1 based not 0 based; 0 means "never saw" in vclocks, whereas 0-based it would mean "first elem"
                val idx =
                  endTimes.search(startTime.minus(1, ChronoUnit.NANOS)) match
                    case Searching.Found(foundIndex) => foundIndex + 1
                    case Searching.InsertionPoint(insertionPoint) =>
                      insertionPoint // idx of first end time that is >= our start
                key -> idx.toLong
              .filter(_._2 != 0)
              .toMap
          simClocks += VClock(simClockKVs.updated(self, selfIdx))

        var idx = 0
        records(self).mapInPlace: rec =>
          rec.copy(clock = rec.clock.merge(simClocks(idx))).tap(_ => idx += 1)
    end if

    val dataValue =
      TLAValueFunction:
        records.view
          .map: (self, records) =>
            (self, TLAValueTuple(records.view.map(_.toTLAValue).toVector))
          .toMap

    os.write.over(
      destDir / s"${modelName}ValidateData.bin",
      dataValue.asTLCBinFmt,
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
      allStringsValue.asTLCBinFmt,
    )
  end generate

object JSONToTLA:
  def apply(modelName: String, destDir: os.Path): JSONToTLA =
    new JSONToTLA(
      modelName = modelName,
      allPaths = true,
      destDir = destDir,
      tlaExtends = Set(
        "Sequences",
        "Integers",
        "TLC",
        "TLCExt",
        "IOUtils",
        "FiniteSetsExt",
      ),
      actionRenamings = Map.empty,
      mpcalVariableDefns = Map(".pc" -> MPCalVariable.Local("pc")),
      modelVariableDefns = Set.empty,
      constantDefns = Set.empty,
      modelValues = Set("defaultInitValue"),
      additionalDefns = Nil,
      progressInv = true,
      physicalClocks = false,
    )
