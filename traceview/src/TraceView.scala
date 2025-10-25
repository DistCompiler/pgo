package pgo.traceview

import scala.collection.{View, mutable}

import pgo.util.TLAExprInterpreter.*

import javafx.application.Application
import javafx.beans.property.{
  Property,
  SimpleObjectProperty,
  SimpleStringProperty,
  StringProperty,
}
import javafx.beans.value.{ChangeListener, ObservableValue, WeakChangeListener}
import javafx.event.{ActionEvent, EventHandler}
import javafx.geometry.{Orientation, Pos}
import javafx.scene.control.ScrollPane.ScrollBarPolicy
import javafx.scene.control.{
  Button,
  ComboBox,
  Hyperlink,
  Label,
  ScrollPane,
  Separator,
  SplitPane,
  TextField,
  TextFormatter,
  ToggleButton,
  TreeItem,
  TreeView,
}
import javafx.scene.layout.{
  Border,
  BorderStroke,
  BorderStrokeStyle,
  GridPane,
  HBox,
  Priority,
  StackPane,
  VBox,
}
import javafx.scene.paint.Paint
import javafx.scene.{Node, Scene}
import javafx.stage.Stage
import javafx.util.converter.IntegerStringConverter

final class TraceView extends Application:
  val fileCombo = ComboBox[String]()
  os.list(os.pwd)
    .filter(os.isFile)
    .filter(_.last.endsWith(".bin"))
    .foreach: elem =>
      fileCombo.itemsProperty().get().add(elem.last)
  val defaultLabel = Label("Select a counterexample to view")
  val contentPane = StackPane(defaultLabel)

  fileCombo
    .valueProperty()
    .addListener:
      new ChangeListener[String]:
        def changed(
            observable: ObservableValue[? <: String],
            oldValue: String,
            newValue: String,
        ): Unit =
          val children = contentPane.getChildren()
          children.clear()
          val path = os.pwd / newValue
          if os.exists(path)
          then
            children.add(
              TraceView
                .Explorer(StateSpace.fromFile(path), valueRenderWidthProp)
                .pane,
            )
          else children.add(defaultLabel)

  val valueRenderWidthProp = SimpleObjectProperty[Integer](80)

  def start(primaryStage: Stage): Unit =
    primaryStage.setTitle(s"TraceView ${os.pwd.toString}")
    primaryStage.setMinWidth(640)
    primaryStage.setMinHeight(480)
    primaryStage.setMaximized(true)
    primaryStage.setScene:
      Scene:
        val valueRenderWidthBox = TextField()
        val valueRenderWidthFormatter = TextFormatter(IntegerStringConverter())
        valueRenderWidthFormatter
          .valueProperty()
          .bindBidirectional(valueRenderWidthProp)
        valueRenderWidthBox.setPrefColumnCount(3)
        valueRenderWidthBox.setTextFormatter(valueRenderWidthFormatter)
        val menuBar = HBox(
          Label("Viewing: "),
          fileCombo,
          Separator(Orientation.VERTICAL),
          Label("Value render width: "),
          valueRenderWidthBox,
        )
        menuBar.setAlignment(Pos.CENTER_LEFT)
        val vbox = VBox(
          menuBar,
          Separator(Orientation.HORIZONTAL),
          contentPane,
        )
        VBox.setVgrow(contentPane, Priority.ALWAYS)

        vbox
    primaryStage.show()
  end start
end TraceView

object TraceView:
  final class Explorer(
      val stateSpace: StateSpace,
      val valueRenderWidthProp: Property[Integer],
  ) extends ExplorerAPI:
    explorer =>
    val displayDepth = SimpleObjectProperty[Integer](1)

    private val selectAState = Label("Select a state to view details here.")
    private val explorerGrid = GridPane()
    private val explorerGridScroll = ScrollPane(explorerGrid)
    explorerGridScroll.setFitToWidth(true)
    explorerGridScroll.setHbarPolicy(ScrollBarPolicy.NEVER)
    explorerGridScroll.setVbarPolicy(ScrollBarPolicy.AS_NEEDED)
    VBox.setVgrow(explorerGridScroll, Priority.ALWAYS)

    private val bottomModButtons = locally:
      val showMoreButton = Button("+1 Row")
      val maxStateDepth = stateSpace.deepestStalledStates.view
        .map(_.depth)
        .maxOption
        .getOrElse(0)
      end maxStateDepth
      showMoreButton
        .onActionProperty()
        .setValue:
          new EventHandler[ActionEvent]:
            def handle(event: ActionEvent): Unit =
              if displayDepth.get() < maxStateDepth
              then displayDepth.set(displayDepth.get() + 1)

      val showLessButton = Button("-1 Row")
      showLessButton
        .onActionProperty()
        .setValue:
          new EventHandler[ActionEvent]:
            def handle(event: ActionEvent): Unit =
              if displayDepth.get() > 1
              then displayDepth.set(displayDepth.get() - 1)

      val levelsShown = TextField()
      val levelsShownFormatter = TextFormatter(IntegerStringConverter())
      levelsShownFormatter.valueProperty().bindBidirectional(displayDepth)
      levelsShown.setPrefColumnCount(3)
      levelsShown.setTextFormatter(levelsShownFormatter)

      val revealStalledStatesButton = Button("Reveal stalled states")
      revealStalledStatesButton
        .onActionProperty()
        .setValue:
          new EventHandler[ActionEvent]:
            def handle(event: ActionEvent): Unit =
              // "state depth" vs display depth, the axes go in opposite directions
              // - "display depth" --> how many rows
              // - "state depth" -> how far from TLC init state
              val stalledStates = stateSpace.deepestStalledStates.view
                .flatMap(_.successorOperations)
                .toSet

              val stateDepthNeeded = stateSpace.states.values.view
                .filter(_.successorOperations.exists(stalledStates))
                .map(_.depth)
                .min

              // + 1 because display depth is 1 based
              val displayDepthNeeded = maxStateDepth - stateDepthNeeded + 1
              displayDepth.setValue(
                displayDepthNeeded.max(displayDepth.getValue()),
              )

      val box = HBox(
        showMoreButton,
        showLessButton,
        Separator(Orientation.VERTICAL),
        Label("Showing levels "),
        levelsShown,
        Label(
          s"out of $maxStateDepth",
        ),
        Separator(Orientation.VERTICAL),
        revealStalledStatesButton,
      )
      box.setAlignment(Pos.CENTER_LEFT)

      box
    end bottomModButtons

    private val recordView = StackPane(selectAState)
    val pane = SplitPane(
      VBox(
        explorerGridScroll,
        Separator(Orientation.HORIZONTAL),
        bottomModButtons,
      ),
      recordView,
    )
    pane.orientationProperty().setValue(Orientation.VERTICAL)

    private val detailCache = mutable.HashMap[stateSpace.TraceRecord, Node]()
    val selectedRecordId = SimpleStringProperty("")
    selectedRecordId.addListener:
      new ChangeListener[String]:
        def changed(
            observable: ObservableValue[? <: String],
            oldValue: String,
            newValue: String,
        ): Unit =
          recordView.getChildren().clear()
          val record = stateSpace.TraceRecord.byShortId(newValue)
          val detail = detailCache.getOrElseUpdate(
            record,
            StateDetail(explorer, record).pane,
          )
          recordView.getChildren().add(detail)

    private val focusedStateProperties = mutable.HashMap[Int, StringProperty]()

    def focusedStateAtDepth(depth: Int): StringProperty =
      focusedStateProperties.getOrElseUpdate(
        depth, {
          val prop = SimpleStringProperty("")
          prop.addListener:
            new ChangeListener[String]:
              def changed(
                  observable: ObservableValue[? <: String],
                  oldValue: String,
                  newValue: String,
              ): Unit =
                rebuildGraph()
          prop
        },
      )

    extension (traceRecord: stateSpace.TraceRecord)
      private def hasFocus: Boolean =
        focusedStateAtDepth(traceRecord.depth).get() == traceRecord.shortId
      private def omittedDueToFocus: Boolean =
        val theFocus = focusedStateAtDepth(traceRecord.depth).get()
        theFocus != "" && theFocus != traceRecord.shortId
      private def cellUI(alreadySeen: Boolean): Node =
        val nodeLabel =
          if alreadySeen
          then traceRecord.shortId
          else traceRecord.descriptiveLabel
        val nodeLabelWithFocus =
          if hasFocus
          then s"> $nodeLabel"
          else nodeLabel
        val node = Hyperlink(nodeLabelWithFocus)
        node.setTextFill(Paint.valueOf("black"))
        node.onActionProperty.setValue:
          new EventHandler[ActionEvent]:
            def handle(event: ActionEvent): Unit =
              selectedRecordId.setValue(traceRecord.shortId)
              node.setVisited(false)
        node
      end cellUI
      private def addToDisplay(
          rowIdx: Int,
          xPos: Int,
          alreadySeen: Boolean,
      ): Node =
        val treeDepth = displayDepth.get() - rowIdx
        val cell = StackPane(traceRecord.cellUI(alreadySeen))
        cell.setBorder(
          Border(BorderStroke(null, BorderStrokeStyle.SOLID, null, null)),
        )
        cell.setAlignment(Pos.CENTER_LEFT)
        GridPane.clearConstraints(cell)
        GridPane.setRowIndex(cell, rowIdx)
        GridPane.setRowSpan(cell, 1)
        GridPane.setColumnIndex(cell, xPos)
        explorerGrid.getChildren().add(cell)
        cell
      end addToDisplay

    private def rebuildGraph(): Unit =
      val nodesSeen = mutable.HashSet[stateSpace.TraceRecord]()
      val depth = displayDepth.get()
      require(depth >= 1)
      val gridChildren = explorerGrid.getChildren()
      gridChildren.clear()

      var leftNodes = mutable
        .HashMap[Int, (traceRecord: stateSpace.TraceRecord, node: Node)]()

      val totalCols = stateSpace.deepestStalledStates.foldLeft(0):
        (xPos, traceRecord) =>
          def addNode(
              traceRecord: stateSpace.TraceRecord,
              rowIdx: Int,
              xPos: Int,
          ): Int =
            // If we're not focused, remove ourselves from rendering
            val theFocus = focusedStateAtDepth(traceRecord.depth).get()
            if theFocus != "" && theFocus != traceRecord.shortId
            then return xPos

            // If the same state is repeated to our left, even if it's in a different group,
            // we can merge the columns so we see the diamond-shape convergence, rather
            // then 2 compressed trees with very similar contents.
            leftNodes.get(rowIdx) match
              case None           =>
              case Some(leftNode) =>
                if leftNode.traceRecord == traceRecord
                then
                  GridPane.setColumnSpan(
                    leftNode.node,
                    GridPane.getColumnSpan(leftNode.node) + 1,
                  )
                  (rowIdx + 1 to displayDepth.get()).foreach: i =>
                    leftNodes
                      .get(i)
                      .foreach: leftNode =>
                        GridPane.setColumnSpan(
                          leftNode.node,
                          GridPane.getColumnSpan(leftNode.node) + 1,
                        )
                  return xPos + 1

            val hadSeen = nodesSeen(traceRecord)
            nodesSeen += traceRecord
            val node = traceRecord.addToDisplay(rowIdx, xPos, hadSeen)
            val xPosNext =
              if rowIdx + 1 < displayDepth.get()
              then
                val childrenNextXPos = traceRecord.predecessorRecords
                  .filter(_ != traceRecord)
                  .foldLeft(xPos): (xPos, traceRecord) =>
                    addNode(traceRecord, rowIdx + 1, xPos)
                val actualWidth = (childrenNextXPos - xPos).max(1)
                GridPane.setColumnSpan(node, actualWidth)
                xPos + actualWidth
              else
                GridPane.setColumnSpan(node, 1)
                xPos + 1
            leftNodes(rowIdx) = (traceRecord = traceRecord, node = node)
            xPosNext
          end addNode
          val nextXPos = addNode(traceRecord, 0, xPos)
          nextXPos
      end totalCols
    end rebuildGraph
    rebuildGraph()
    displayDepth.addListener:
      new ChangeListener[Number]:
        def changed(
            observable: ObservableValue[? <: Number],
            oldValue: Number,
            newValue: Number,
        ): Unit =
          rebuildGraph()
  end Explorer

  trait ExplorerAPI:
    val stateSpace: StateSpace
    val valueRenderWidthProp: Property[Integer]

    def focusedStateAtDepth(depth: Int): Property[String]
  end ExplorerAPI

  final class StateDetail(
      val explorerAPI: ExplorerAPI,
      val traceRecord: explorerAPI.stateSpace.TraceRecord,
  ):
    private val label = Label(
      s"${traceRecord.descriptiveLabel} depth=${traceRecord.depth}",
    )
    private val focusToggle = ToggleButton("Focus")
    private val depthFocusState =
      explorerAPI.focusedStateAtDepth(traceRecord.depth)
    focusToggle.setSelected(depthFocusState.getValue() == traceRecord.shortId)
    focusToggle
      .onActionProperty()
      .setValue:
        new EventHandler[ActionEvent]:
          def handle(event: ActionEvent): Unit =
            if depthFocusState.getValue() == traceRecord.shortId
            then depthFocusState.setValue("")
            else depthFocusState.setValue(traceRecord.shortId)
    val focusListener = new ChangeListener[String]:
      def changed(
          observable: ObservableValue[? <: String],
          oldValue: String,
          newValue: String,
      ): Unit =
        focusToggle.setSelected(newValue == traceRecord.shortId)
    depthFocusState.addListener(WeakChangeListener(focusListener))

    private def predecessorRecordsAccountingForFocus
        : List[explorerAPI.stateSpace.TraceRecord] =
      val focusBelow =
        explorerAPI.focusedStateAtDepth(traceRecord.depth - 1).getValue()
      if focusBelow == ""
      then traceRecord.predecessorRecords.toList
      else traceRecord.predecessorRecords.filter(_.shortId == focusBelow).toList
    end predecessorRecordsAccountingForFocus

    private val predecessorsProp =
      SimpleObjectProperty[List[explorerAPI.stateSpace.TraceRecord]]:
        predecessorRecordsAccountingForFocus
    val predecessorsFocusListener = new ChangeListener[String]:
      def changed(
          observable: ObservableValue[? <: String],
          oldValue: String,
          newValue: String,
      ): Unit =
        val newPreds = predecessorRecordsAccountingForFocus
        predecessorsProp.setValue(predecessorRecordsAccountingForFocus)
    explorerAPI
      .focusedStateAtDepth(traceRecord.depth - 1)
      .addListener(WeakChangeListener(predecessorsFocusListener))

    private val treeViewRoot = makeTLAValueTreeItem(
      traceRecord.tlaValue,
      prevValuesProp = predecessorsProp.map: predecessors =>
        if predecessors.isEmpty
        then List(PrevValue.Missing)
        else
          predecessors.map: predecessor =>
            PrevValue.Known(predecessor.tlaValue),
    )
    private val treeView = TreeView(treeViewRoot)
    treeView.setShowRoot(false)
    private val menuBox =
      HBox(label, Separator(Orientation.VERTICAL), focusToggle)
    menuBox.setAlignment(Pos.CENTER_LEFT)
    val pane = VBox(
      menuBox,
      treeView,
    )
    VBox.setVgrow(treeView, Priority.ALWAYS)

    private enum PrevValue:
      case Unknown
      case Known(value: TLAValue)
      case Missing

      def filter(pred: TLAValue => Boolean): PrevValue =
        this match
          case Unknown                     => Unknown
          case Known(value) if pred(value) =>
            Known(value)
          case Known(_) => Unknown
          case Missing  => Missing

      def flatMap(fn: TLAValue => Option[TLAValue]): PrevValue =
        this match
          case Unknown      => Unknown
          case Known(value) =>
            fn(value) match
              case Some(value) => Known(value)
              case None        => Missing
          case Missing => Unknown
    end PrevValue

    private object PrevValue:
      extension (prevValues: List[PrevValue])
        def flattenPrevValues: List[PrevValue] =
          prevValues.distinct
    end PrevValue

    private class TreeItemWithTrunc(
        labelFn: => String,
        prevMarkerProp: ObservableValue[String] = SimpleStringProperty(""),
        prevValuesProp: ObservableValue[List[PrevValue]] = SimpleObjectProperty(
          Nil,
        ),
        children: => View[TreeItem[String]] = View.empty,
    ) extends TreeItem[String]:
      def truncatedLabel: String =
        val labelStr: String = s"${prevMarkerProp.getValue()}$labelFn"
        if labelStr.size > explorerAPI.valueRenderWidthProp.getValue()
        then
          s"${labelStr.take(explorerAPI.valueRenderWidthProp.getValue() - 1)}..."
        else labelStr
      end truncatedLabel
      setValue(truncatedLabel)
      children.foreach(getChildren().add)
      val renderWidthListener = new ChangeListener[Number]:
        def changed(
            observable: ObservableValue[? <: Number],
            oldValue: Number,
            newValue: Number,
        ): Unit =
          setValue(truncatedLabel)
      end renderWidthListener
      explorerAPI.valueRenderWidthProp.addListener(
        WeakChangeListener(renderWidthListener),
      )
      prevMarkerProp.addListener:
        new ChangeListener[String]:
          def changed(
              observable: ObservableValue[? <: String],
              oldValue: String,
              newValue: String,
          ): Unit =
            setValue(truncatedLabel)
      val prevValuesListener = new ChangeListener[List[PrevValue]]:
        def changed(
            observable: ObservableValue[? <: List[PrevValue]],
            oldValue: List[PrevValue],
            newValue: List[PrevValue],
        ): Unit =
          getChildren().clear()
          children.foreach(getChildren().add)
      end prevValuesListener
      prevValuesProp.addListener(WeakChangeListener(prevValuesListener))
    end TreeItemWithTrunc

    private def makeTLAValueTreeItem(
        value: TLAValue,
        prefix: String = "",
        prevValuesProp: ObservableValue[List[PrevValue]],
    ): TreeItem[String] =
      val prevMarkerProp = prevValuesProp.map: prevValues =>
        val builder = StringBuilder()
        if prevValues.contains(PrevValue.Missing)
        then builder += '+'
        if prevValues.exists:
            case PrevValue.Known(prev) if prev != value => true
            case _                                      => false
        then builder += '~'
        if builder.nonEmpty
        then builder += ' '
        builder.result()
      value match
        case leaf: (TLAValueModel | TLAValueBool | TLAValueNumber |
              TLAValueString) =>
          TreeItemWithTrunc(
            labelFn = s"$prefix${leaf.toString}",
            prevValuesProp = prevValuesProp,
            prevMarkerProp = prevMarkerProp,
          )
        case TLAValueSet(_value) =>
          TreeItemWithTrunc(
            labelFn = s"${prefix}${value.toString}",
            prevMarkerProp = prevMarkerProp,
            prevValuesProp = prevValuesProp,
            children = _value.toArray.sortInPlace.view
              .map: elem =>
                makeTLAValueTreeItem(
                  elem,
                  "",
                  prevValuesProp.map: prevValues =>
                    prevValues
                      .map: prevValue =>
                        prevValue
                          .filter(_.isInstanceOf[TLAValueSet])
                          .flatMap: prev =>
                            if prev.contains(elem)
                            then Some(elem)
                            else None
                      .flattenPrevValues,
                )
              .++(
                prevValuesProp
                  .getValue()
                  .collect:
                    case PrevValue.Known(TLAValueSet(oldValues)) =>
                      oldValues -- _value
                  .flatten
                  .sorted
                  .map: removedElem =>
                    makeTLAValueTreeItem(
                      removedElem,
                      "! ",
                      SimpleObjectProperty(Nil),
                    ),
              ),
          )
        case TLAValueTuple(_value) =>
          TreeItemWithTrunc(
            labelFn = s"${prefix}${value.toString}",
            prevMarkerProp = prevMarkerProp,
            prevValuesProp = prevValuesProp,
            children = _value.view.zipWithIndex
              .map: (v, idx) =>
                makeTLAValueTreeItem(
                  v,
                  s"[${idx + 1}] = ",
                  prevValuesProp.map: prevValues =>
                    prevValues
                      .map: prevValue =>
                        prevValue
                          .filter(_.isInstanceOf[TLAValueTuple])
                          .flatMap(_.get(idx))
                      .flattenPrevValues,
                )
              .++(
                prevValuesProp
                  .getValue()
                  .view
                  .collect:
                    case PrevValue.Known(TLAValueTuple(oldValues)) =>
                      oldValues.view.zipWithIndex.drop(_value.size)
                  .flatten
                  .iterator
                  .distinct
                  .toArray
                  .sortInPlaceBy(_._2)
                  .view
                  .map: (oldElem, idx) =>
                    makeTLAValueTreeItem(
                      oldElem,
                      s"! [${idx + 1}] = ",
                      SimpleObjectProperty(Nil),
                    ),
              ),
          )
        case TLAValueFunction(_value) =>
          TreeItemWithTrunc(
            labelFn = s"${prefix}${value.toString}",
            prevMarkerProp = prevMarkerProp,
            prevValuesProp = prevValuesProp,
            children = _value.toArray.sortInPlace.view
              .map: (key, v) =>
                makeTLAValueTreeItem(
                  v,
                  s"[$key] = ",
                  prevValuesProp.map: prevValues =>
                    prevValues
                      .map: prevValue =>
                        prevValue
                          .filter(_.isInstanceOf[TLAValueFunction])
                          .flatMap(_.get(key))
                      .flattenPrevValues,
                )
              .++(
                prevValuesProp
                  .getValue()
                  .view
                  .collect:
                    case PrevValue.Known(TLAValueFunction(oldPairs)) =>
                      oldPairs -- _value.keys
                  .flatten
                  .iterator
                  .distinct
                  .toArray
                  .sortInPlace
                  .view
                  .map: (k, v) =>
                    makeTLAValueTreeItem(
                      v,
                      s"! [$k] = ",
                      SimpleObjectProperty(Nil),
                    ),
              ),
          )
        case TLAValueLambda(_) =>
          TreeItemWithTrunc("<lambda>")
    end makeTLAValueTreeItem
  end StateDetail
end TraceView
