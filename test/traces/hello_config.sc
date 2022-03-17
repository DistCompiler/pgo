import pgo.util.TLAExprInterpreter.{TLAValueString,TLAValueLambda}

pgo.PGo.TraceCheckerUserConfig.build { builder =>
  builder.constant("MK_HELLO")(TLAValueLambda {
    case List(TLAValueString(left), TLAValueString(right)) =>
      TLAValueString(left ++ right)
  })
}
