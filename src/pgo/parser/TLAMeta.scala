package pgo.parser

object TLAMeta {
  val reservedWords: Set[String] = Set(
    "ASSUME",
    "ASSUMPTION",
    "AXIOM",
    "CASE",
    "CHOOSE",
    "CONSTANT",
    "CONSTANTS",
    "DOMAIN",
    "ELSE",
    "ENABLED",
    "EXCEPT",
    "EXTENDS",
    "IF",
    "IN",
    "INSTANCE",
    "LET",
    "LOCAL",
    "MODULE",
    "OTHER",
    "SF_",
    "SUBSET",
    "THEN",
    "THEOREM",
    "UNCHANGED",
    "UNION",
    "VARIABLE",
    "VARIABLES",
    "WF_",
    "WITH"
  )

  /** name -> (low precedence, high precedence)
    */
  val prefixOperators: Map[String, (Int, Int)] = Map(
    raw"""UNCHANGED""" -> (4, 15),
    raw"""ENABLED""" -> (4, 15),
    raw"""DOMAIN""" -> (9, 9),
    raw"""SUBSET""" -> (8, 8),
    raw"""\lnot""" -> (4, 4),
    raw"""UNION""" -> (8, 8),
    raw"""\neg""" -> (4, 4),
    raw"""[]""" -> (4, 15),
    raw"""<>""" -> (4, 15),
    raw"""-_""" -> (12, 12),
    raw"""~""" -> (4, 4)
  )

  /** name -> (low precedence, high precedence, left associative)
    */
  val infixOperators: Map[String, (Int, Int, Boolean)] = Map(
    raw"""!!""" -> (9, 13, false),
    raw"""#""" -> (5, 5, false),
    raw"""##""" -> (9, 13, true),
    raw"""$$""" -> (9, 13, true),
    raw"""$$$$""" -> (9, 13, true),
    raw"""%""" -> (10, 11, false),
    raw"""%%""" -> (10, 11, true),
    raw"""&""" -> (13, 13, true),
    raw"""&&""" -> (13, 13, true),
    raw"""(+)""" -> (10, 10, false),
    raw"""(-)""" -> (11, 11, false),
    raw"""(.)""" -> (13, 13, false),
    raw"""(/)""" -> (13, 13, false),
    raw"""(\X)""" -> (13, 13, false),
    raw"""*""" -> (13, 13, true),
    raw"""**""" -> (13, 13, true),
    raw"""+""" -> (10, 10, true),
    raw"""++""" -> (10, 10, true),
    raw"""-""" -> (11, 11, true),
    raw"""-+->""" -> (2, 2, false),
    raw"""--""" -> (11, 11, true),
    raw"""-|""" -> (5, 5, false),
    raw""".""" -> (17, 17, true),
    raw"""..""" -> (9, 9, false),
    raw"""...""" -> (9, 9, false),
    raw"""/""" -> (13, 13, false),
    raw"""//""" -> (13, 13, false),
    raw"""/=""" -> (5, 5, false),
    raw"""/\""" -> (3, 3, true),
    raw"""::=""" -> (5, 5, false),
    raw""":=""" -> (5, 5, false),
    raw""":>""" -> (7, 7, false),
    raw"""<""" -> (5, 5, false),
    raw"""<:""" -> (7, 7, false),
    raw"""<=""" -> (5, 5, false),
    raw"""<=>""" -> (5, 5, false),
    raw"""=""" -> (5, 5, false),
    raw"""=<""" -> (5, 5, false),
    raw"""=>""" -> (1, 1, false),
    raw"""=|""" -> (5, 5, false),
    raw""">""" -> (5, 5, false),
    raw""">=""" -> (5, 5, false),
    raw"""?""" -> (5, 5, false),
    raw"""??""" -> (9, 13, true),
    raw"""@@""" -> (6, 6, true),
    raw"""\""" -> (8, 8, false),
    raw"""\/""" -> (3, 3, true),
    raw"""\approx""" -> (5, 5, false),
    raw"""\asymp""" -> (5, 5, false),
    raw"""\bigcirc""" -> (13, 13, false),
    raw"""\bullet""" -> (13, 13, true),
    raw"""\cap""" -> (8, 8, true),
    raw"""\cdot""" -> (5, 14, true),
    raw"""\circ""" -> (13, 13, true),
    raw"""\cong""" -> (5, 5, false),
    raw"""\cup""" -> (8, 8, true),
    raw"""\div""" -> (13, 13, false),
    raw"""\doteq""" -> (5, 5, false),
    raw"""\equiv""" -> (2, 2, false),
    raw"""\geq""" -> (5, 5, false),
    raw"""\gg""" -> (5, 5, false),
    raw"""\in""" -> (5, 5, false),
    raw"""\intersect""" -> (8, 8, false),
    raw"""\land""" -> (3, 3, false),
    raw"""\leq""" -> (5, 5, false),
    raw"""\ll""" -> (5, 5, false),
    raw"""\lor""" -> (3, 3, false),
    raw"""\notin""" -> (5, 5, false),
    raw"""\o""" -> (13, 13, true),
    raw"""\odot""" -> (13, 13, true),
    raw"""\ominus""" -> (11, 11, true),
    raw"""\oplus""" -> (10, 10, true),
    raw"""\oslash""" -> (13, 13, false),
    raw"""\otimes""" -> (13, 13, true),
    raw"""\prec""" -> (5, 5, false),
    raw"""\preceq""" -> (5, 5, false),
    raw"""\propto""" -> (5, 5, false),
    raw"""\sim""" -> (5, 5, false),
    raw"""\simeq""" -> (5, 5, false),
    raw"""\sqcap""" -> (9, 13, true),
    raw"""\sqcup""" -> (9, 13, true),
    raw"""\sqsubset""" -> (5, 5, false),
    raw"""\sqsubseteq""" -> (5, 5, false),
    raw"""\sqsupset""" -> (5, 5, false),
    raw"""\sqsupseteq""" -> (5, 5, false),
    raw"""\star""" -> (13, 13, true),
    raw"""\subset""" -> (5, 5, false),
    raw"""\subseteq""" -> (5, 5, false),
    raw"""\succ""" -> (5, 5, false),
    raw"""\succeq""" -> (5, 5, false),
    raw"""\supset""" -> (5, 5, false),
    raw"""\supseteq""" -> (5, 5, false),
    raw"""${"\\"}union""" -> (8, 8, true),
    raw"""${"\\"}uplus""" -> (9, 13, true),
    raw"""\wr""" -> (9, 14, false),
    raw"""^""" -> (14, 14, false),
    raw"""^^""" -> (14, 14, false),
    raw"""|""" -> (10, 11, true),
    raw"""|-""" -> (5, 5, false),
    raw"""|=""" -> (5, 5, false),
    raw"""||""" -> (10, 11, true),
    raw"""~>""" -> (2, 2, false)
  )

  /** name -> precedence
    */
  val postfixOperators: Map[String, Int] = Map(
    raw"""^+""" -> 15,
    raw"""^*""" -> 15,
    raw"""^#""" -> 15,
    raw"""'""" -> 15
  )
}
