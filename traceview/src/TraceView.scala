package pgo.traceview

import scala.collection.mutable

import scalafx.Includes.given
import scalafx.application.JFXApp3
import scalafx.scene.{control, layout}

import pgo.util.TLAExprInterpreter.*

object TraceView extends JFXApp3:
  final case class TraceRecord(value: TLAValue):
    def action: TLAValue = value("__action")

    def operationName: String = action("operation_name").asString
    def operationStart: Int = action("op_start").asInt
    def operationEnd: Int = action("op_end").asInt
    def pid: Int = action("pid").asInt

    def successors: Map[Int, TLAValue] =
      value("__successors").asMap.view
        .map: (pid, record) =>
          pid.asInt -> record
        .toMap
    end successors

    def isInitialState: Boolean =
      action == TLAValueTuple(Vector.empty)
    end isInitialState

    def titleString: String =
      if isInitialState
      then "initial state"
      else s"$operationName: pid=$pid, span=[$operationStart, $operationEnd]"
    end titleString
  end TraceRecord

  private val maxValueLabelLength = scalafx.beans.property.IntegerProperty(80)
  private val eventsShown = scalafx.beans.property.IntegerProperty(1)
  private val openSubscriptions =
    mutable.ListBuffer[scalafx.event.subscriptions.Subscription]()

  def makeTLAValueTreeItem(
      value: TLAValue,
      prefix: String = "",
      prevOpt: Option[TLAValue],
  ): control.TreeItem[String] =
    val valueOuter = value
    def shortValueString: String =
      val str = value.toString
      if str.length > maxValueLabelLength()
      then str.take(maxValueLabelLength() - 3) ++ "..."
      else str
    end shortValueString
    def forMaxValueLabelLength(fn: => Unit): Unit =
      fn
      openSubscriptions += maxValueLabelLength.onChange(fn)
    class BaseItem extends control.TreeItem[String]:
      prevOpt match
        case Some(prev) if prev != valueOuter =>
          forMaxValueLabelLength:
            this.value = s"> $prefix$shortValueString"
        case None =>
          forMaxValueLabelLength:
            this.value = s"+ $prefix$shortValueString"
        case _ =>
          forMaxValueLabelLength:
            this.value = s"$prefix$shortValueString"
    end BaseItem
    value match
      case leaf: (TLAValueModel | TLAValueBool | TLAValueNumber |
            TLAValueString) =>
        new BaseItem
      case TLAValueSet(_value) =>
        new BaseItem:
          children ++= _value.toArray.sortInPlace
            .map: elem =>
              makeTLAValueTreeItem(
                elem,
                "",
                prevOpt.flatMap: prev =>
                  if prev.contains(elem)
                  then Some(elem)
                  else None,
              )
      case TLAValueTuple(_value) =>
        new BaseItem:
          children ++= _value.iterator.zipWithIndex
            .map: (v, idx) =>
              makeTLAValueTreeItem(
                v,
                prefix = s"[${idx + 1}] = ",
                prevOpt.flatMap(_.get(idx)),
              )
      case TLAValueFunction(_value) =>
        new BaseItem:
          children ++= _value.toArray.sortInPlace.iterator
            .map: (key, v) =>
              makeTLAValueTreeItem(
                v,
                prefix = s"[$key] = ",
                prevOpt.flatMap(_.get(key)),
              )
      case TLAValueLambda(_) =>
        new BaseItem
  end makeTLAValueTreeItem

  def makeTraceRecordTreeItem(
      idx: Int,
      traceRecord: TraceRecord,
      prevOpt: Option[TLAValue],
  ): control.TreeItem[String] =
    new control.TreeItem[String]:
      value = s"$idx -- ${traceRecord.titleString}"
      children += makeTLAValueTreeItem(
        traceRecord.value,
        prefix = "record = ",
        prevOpt,
      )
  end makeTraceRecordTreeItem

  private var hasView = false
  def makeView(dumpFile: os.Path): Unit =
    locally:
      // Clean things up between reloads, so we don't leak memory
      hasView = true
      openSubscriptions.foreach(_.cancel())
      openSubscriptions.clear()
      eventsShown.value = 1

    val value = TLAValue.parseFromTLCBinFmtGZIP(os.read.stream(dumpFile))
    value match
      case TLAValueTuple(seq) =>
        val dumpFileStr = dumpFile.relativeTo(os.pwd).toString
        stage.title = s"TraceView: $dumpFileStr"
        object treeView extends control.TreeView[String]:
          hgrow = layout.Priority.Always
          vgrow = layout.Priority.Always
          showRoot = false
          cellFactory =
            locally[javafx.util.Callback[javafx.scene.control.TreeView[
              String,
            ], javafx.scene.control.TreeCell[String]]]: (tc) =>
              new javafx.scene.control.TreeCell[String]:
                def highlightThis(color: String): Unit =
                  setBackground:
                    scalafx.scene.layout.Background(
                      Array(
                        scalafx.scene.layout.BackgroundFill(
                          scalafx.scene.paint.Paint.valueOf(color),
                          scalafx.scene.layout.CornerRadii.Empty,
                          scalafx.geometry.Insets.Empty,
                        ),
                      ),
                    )

                def unhighlightThis(): Unit =
                  highlightThis("white")

                override protected def updateItem(
                    item: String,
                    empty: Boolean,
                ): Unit =
                  super.updateItem(item, empty)
                  if empty || (item eq null)
                  then
                    unhighlightThis()
                    this.setText(null)
                    this.setGraphic(null)
                  else
                    this.setText(item)
                    if !this.isSelected()
                    then
                      if item.startsWith("> ")
                      then highlightThis("yellow")
                      else if item.startsWith("+ ")
                      then highlightThis("yellowgreen")
                      else unhighlightThis()
                    else highlightThis("grey")
                end updateItem
          root = new control.TreeItem[String]:
            def updateChildren(): Unit =
              if children.size > eventsShown()
              then children.dropRightInPlace(children.size - eventsShown())
              else if children.size < eventsShown()
              then
                (children.size until eventsShown()).foreach: idx =>
                  val rseq = seq.view.reverse
                  if idx <= seq.size
                  then
                    children += makeTraceRecordTreeItem(
                      rseq.size - idx,
                      TraceRecord(rseq(idx)),
                      if rseq.indices.contains(idx + 1) then Some(rseq(idx + 1))
                      else None,
                    )
            end updateChildren

            updateChildren()
            openSubscriptions += eventsShown.onChange(updateChildren())
        end treeView

        val view = new layout.VBox:
          children = Seq(
            control.Label(s"Viewing $dumpFileStr"),
            new control.SplitPane:
              vgrow = layout.Priority.Always
              spacing = 5
              // TODO: not sure if this works
              setDividerPosition(0, 1)
              items ++= Seq(
                treeView,
                new layout.VBox:
                  spacing = 5
                  alignment = scalafx.geometry.Pos.Center

                  // Top aligned items
                  object eventsShownLabel extends control.Label:
                    def updateField(): Unit =
                      text = s"Events shown: ${eventsShown()} / ${seq.size}"
                    updateField()
                    openSubscriptions += eventsShown.onChange(updateField())
                  end eventsShownLabel
                  object incDecButtons extends layout.HBox:
                    spacing = 3
                    alignment = scalafx.geometry.Pos.Center

                    private trait ButtonDisableLow:
                      self: control.Button =>
                      def disableThreshold: Int
                      private def updateDisable(): Unit =
                        self.setDisable(eventsShown() <= disableThreshold)

                      updateDisable()
                      openSubscriptions += eventsShown.onChange(updateDisable())
                    end ButtonDisableLow

                    private trait ButtonDisableHigh:
                      self: control.Button =>
                      def disableThreshold: Int
                      private def updateDisable(): Unit =
                        self.setDisable(eventsShown() >= disableThreshold)

                      updateDisable()
                      openSubscriptions += eventsShown.onChange(updateDisable())
                    end ButtonDisableHigh

                    children = Seq(
                      new control.Button("+1") with ButtonDisableHigh:
                        def disableThreshold: Int = seq.size
                        onAction.value =
                          _ => eventsShown.value = eventsShown() + 1
                      ,
                      new control.Button("-1") with ButtonDisableLow:
                        def disableThreshold: Int = 1
                        onAction.value = _ =>
                          if eventsShown() > 1
                          then eventsShown.value = eventsShown() - 1
                      ,
                      new control.Separator:
                        orientation = scalafx.geometry.Orientation.Vertical
                      ,
                      new control.Button("+5") with ButtonDisableHigh:
                        def disableThreshold: Int = seq.size - 4
                        onAction.value =
                          _ => eventsShown.value = eventsShown() + 5
                      ,
                      new control.Button("-5") with ButtonDisableLow:
                        def disableThreshold: Int = 5
                        onAction.value = _ =>
                          if eventsShown() > 5
                          then eventsShown.value = eventsShown() - 5,
                    )
                  end incDecButtons
                  object showPossibleAltPositionsButton
                      extends control.Button(
                        "Show positions where failed action(s) could happen",
                      ):
                    textAlignment = scalafx.scene.text.TextAlignment.Center
                    wrapText = true
                    onAction.value = _ =>
                      val records = seq.view.map(TraceRecord(_)).reverse
                      val tip = records.head
                      val tipSuccessors = tip.successors.toSet
                      assert(!tip.isInitialState)

                      val countToShow = records.view.tail
                        .takeWhile: rec =>
                          rec.successors.exists(tipSuccessors)
                        .size + 1

                      eventsShown.value = countToShow
                  end showPossibleAltPositionsButton

                  // Bottom aligned items
                  object loadAnotherTraceButton
                      extends control.Button("Load another trace"):
                    onAction() = evt => chooseDumpFile()
                  end loadAnotherTraceButton
                  object maxValueLabelLengthField extends layout.HBox:
                    alignment = scalafx.geometry.Pos.Center
                    spacing = 5
                    children = Seq(
                      control.Label("Value text cap:"),
                      new control.TextField:
                        text = maxValueLabelLength().toString()
                        prefColumnCount = 3
                        onAction = _ =>
                          text().toIntOption match
                            case Some(i) if i >= 10 =>
                              maxValueLabelLength.value = i
                            case _ =>
                              text.value = maxValueLabelLength().toString(),
                    )
                  end maxValueLabelLengthField

                  children = Seq(
                    eventsShownLabel,
                    incDecButtons,
                    showPossibleAltPositionsButton,
                    new layout.Pane:
                      vgrow = layout.Priority.Always
                    ,
                    loadAnotherTraceButton,
                    maxValueLabelLengthField,
                  ),
              ),
          )

        stage.scene().root = view
      case _ => ???
  end makeView

  def chooseDumpFile(): Unit =
    val fileChooser = new scalafx.stage.FileChooser:
      title = "Choose Trace Dump File"
      extensionFilters ++= Seq(
        scalafx.stage.FileChooser.ExtensionFilter("Trace Dump File", "*.bin"),
      )

    val dumpFile = fileChooser.showOpenDialog(stage)
    if dumpFile ne null
    then makeView(os.Path(dumpFile))
    else if !hasView
    then scalafx.application.Platform.exit()
  end chooseDumpFile

  def start(): Unit =
    stage = new JFXApp3.PrimaryStage:
      maximized = true
      scene = new scalafx.scene.Scene:
        title = "TraceView"
        root = new control.Label("Starting...")

    chooseDumpFile()
  end start
end TraceView
