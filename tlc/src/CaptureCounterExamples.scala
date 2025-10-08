package pgo.util

import scala.collection.mutable
import scala.util.Using
import scala.util.Using.Releasable

import tla2sany.semantic.SemanticNode
import tlc2.tool.{Action, TLCState}
import tlc2.util.IStateWriter.Visualization
import tlc2.util.{BitVector, IStateWriter}
import tlc2.value.ValueOutputStream
import tlc2.value.impl.{
  FcnRcdValue,
  RecordValue,
  StringValue,
  TupleValue,
  Value,
}
import util.UniqueString

final class CaptureCounterExamples() extends IStateWriter:
  captureCounterExamples =>
  private val dumpFile = os.pwd / "CaptureCounterExamples.bin"

  // Tricky: if someone Ctrl^C TLC, I want to see the counterexample anyway.
  // Add a "fake" call to .close() so it shows up.
  private var didClose = false
  Runtime
    .getRuntime()
    .addShutdownHook:
      new Thread:
        override def run(): Unit = captureCounterExamples.synchronized:
          if !didClose
          then
            println(s"JVM shutdown! Saving states so far to $dumpFile")
            close()

  def isDot(): Boolean = false
  def isNoop(): Boolean = false
  def isConstrained(): Boolean = false
  def getDumpFileName(): String = dumpFile.last

  def snapshot(): Unit = ()

  def writeState(state: TLCState): Unit =
    writeInitStateImpl(state)
  def writeState(
      state: TLCState,
      successor: TLCState,
      stateFlags: Short,
  ): Unit =
    writeStateImpl(
      state = state,
      successor = successor,
      stateFlags = stateFlags,
    )
  def writeState(
      state: TLCState,
      successor: TLCState,
      stateFlags: Short,
      action: Action,
  ): Unit =
    writeStateImpl(
      state = state,
      successor = successor,
      stateFlags = stateFlags,
      action = action,
    )
  def writeState(
      state: TLCState,
      successor: TLCState,
      stateFlags: Short,
      vis: Visualization,
  ): Unit =
    writeStateImpl(
      state = state,
      successor = successor,
      stateFlags = stateFlags,
      vis = vis,
    )
  def writeState(
      state: TLCState,
      successor: TLCState,
      stateFlags: Short,
      action: Action,
      semanticNode: SemanticNode,
  ): Unit =
    writeStateImpl(
      state = state,
      successor = successor,
      stateFlags = stateFlags,
      action = action,
      semanticNode = semanticNode,
    )
  def writeState(
      state: TLCState,
      successor: TLCState,
      actionChecks: BitVector,
      start: Int,
      length: Int,
      stateFlags: Short,
  ): Unit =
    writeStateImpl(
      state = state,
      successor = successor,
      actionChecks = actionChecks,
      start = start,
      length = length,
      stateFlags = stateFlags,
    )
  def writeState(
      state: TLCState,
      successor: TLCState,
      actionChecks: BitVector,
      start: Int,
      length: Int,
      stateFlags: Short,
      vis: Visualization,
  ): Unit =
    writeStateImpl(
      state = state,
      successor = successor,
      actionChecks = actionChecks,
      start = start,
      length = length,
      stateFlags = stateFlags,
      vis = vis,
    )

  private val stateFingerprintsWitnessed = mutable.HashSet[Long]()
  private val statesWitnessed = mutable.ListBuffer[TLCState]()
  private val transitionsWitnessed = mutable.HashSet[(Long, Long)]()
  private val transitionsWitnessedBuffer = mutable.ListBuffer[(Long, Long)]()

  private def witnessState(state: TLCState): Unit = synchronized:
    val fingerprint = state.fingerPrint()
    if !stateFingerprintsWitnessed(fingerprint)
    then
      stateFingerprintsWitnessed += fingerprint
      val alias = state.evalStateLevelAlias()
      statesWitnessed += alias
  end witnessState

  private def witnessTransition(state: TLCState, successor: TLCState): Unit =
    val fingerprint1 = state.fingerPrint()
    val fingerprint2 = successor.fingerPrint()
    val transition = (fingerprint1, fingerprint2)

    if !transitionsWitnessed(transition)
    then
      transitionsWitnessed += transition
      transitionsWitnessedBuffer += transition
  end witnessTransition

  private def writeInitStateImpl(state: TLCState): Unit = synchronized:
    witnessState(state)
  end writeInitStateImpl

  private def writeStateImpl(
      state: TLCState,
      successor: TLCState,
      actionChecks: BitVector | Null = null,
      start: Int = 0,
      length: Int = 0,
      stateFlags: Short,
      vis: Visualization = Visualization.DEFAULT,
      action: Action | Null = null,
      semanticNode: SemanticNode | Null = null,
  ): Unit = synchronized:
    witnessState(state)
    witnessState(successor)
    witnessTransition(state, successor)
  end writeStateImpl

  def close(): Unit = synchronized:
    if didClose
    then return
    didClose = true

    val states =
      FcnRcdValue(
        statesWitnessed.view
          .map: state =>
            StringValue(state.fingerPrint().toString())
          .toArray[Value],
        statesWitnessed.view
          .map: state =>
            state match
              case state: RecordValue.PrintTLCState =>
                // Empirically found by tracing what TLC gives us: a record wrapped in a state interface.
                // Pull out the record, because the state reports "correct" vars not affected by ALIAS
                // (and our use case relies on ALIAS values)
                state.getRecord()
              case state =>
                val names = state.getVars().map(_.getName())
                RecordValue(
                  names,
                  names.map: name =>
                    state.lookup(name).asInstanceOf[Value],
                  false,
                )
          .toArray[Value],
        false,
      )
    val pairs =
      TupleValue:
        transitionsWitnessedBuffer.view
          .map: (from, to) =>
            TupleValue(
              Array[Value](
                StringValue(from.toString()),
                StringValue(to.toString()),
              ),
            )
          .toArray[Value]
    val root = RecordValue(
      Array[UniqueString](UniqueString.of("states"), UniqueString.of("pairs")),
      Array[Value](states, pairs),
      false,
    )
    root.deepNormalize()
    given Releasable[ValueOutputStream] with
      def release(resource: ValueOutputStream): Unit =
        resource.close()
    Using.resource(ValueOutputStream(dumpFile.last)): out =>
      root.write(out)
  end close
end CaptureCounterExamples
