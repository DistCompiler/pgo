package dqueue

import "github.com/UBC-NSS/pgo/distsys"

type Constants struct {
  BUFFER_SIZE distsys.TLAValue
  NUM_CONSUMERS distsys.TLAValue
  PRODUCER distsys.TLAValue
}

func NUM_NODES(constants Constants) distsys.TLAValue {
  return distsys.TLA_PlusSymbol(constants.NUM_CONSUMERS, distsys.NewTLANumber(1))
}

func AConsumer(self distsys.TLAValue, constants0 Constants, net distsys.ArchetypeResource, proc distsys.ArchetypeResource) error {
  var err error
  
  c: {
    sectionCtx := distsys.NewPCalSectionContext()
    var exprReads []distsys.TLAValue
    exprReads, err = distsys.WhileCatchingPanics(func() distsys.TLAValue { return distsys.TLA_TRUE })
    if err != nil {
      sectionCtx.Abort()
      if err == distsys.Aborted {
        goto c
      } else {
        return err
      }
    }
    if exprReads[0].IsTrue() {
      switch err = sectionCtx.Commit(); err {
      case error(nil):
        goto c1
      case distsys.Aborted:
        goto c
      default:
        return err
      }
    } else {
      // no statements
    }
    // no statements
  }
  c1: {
    sectionCtx0 := distsys.NewPCalSectionContext()
    var exprReads0 []distsys.TLAValue
    exprReads0, err = distsys.WhileCatchingPanics(func() distsys.TLAValue { return self }, func() distsys.TLAValue { return constants0.PRODUCER })
    if err != nil {
      sectionCtx0.Abort()
      if err == distsys.Aborted {
        goto c1
      } else {
        return err
      }
    }
    err = sectionCtx0.Write(net, exprReads0[1:], exprReads0[0])
    if err != nil {
      sectionCtx0.Abort()
      if err == distsys.Aborted {
        goto c1
      } else {
        return err
      }
    }
    switch err = sectionCtx0.Commit(); err {
    case error(nil):
      goto c2
    case distsys.Aborted:
      goto c1
    default:
      return err
    }
  }
  c2: {
    sectionCtx1 := distsys.NewPCalSectionContext()
    var exprReads1 []distsys.TLAValue
    exprReads1, err = distsys.WhileCatchingPanics(func() distsys.TLAValue { return sectionCtx1.Read(net, []distsys.TLAValue{self}) })
    if err != nil {
      sectionCtx1.Abort()
      if err == distsys.Aborted {
        goto c2
      } else {
        return err
      }
    }
    err = sectionCtx1.Write(proc, exprReads1[1:], exprReads1[0])
    if err != nil {
      sectionCtx1.Abort()
      if err == distsys.Aborted {
        goto c2
      } else {
        return err
      }
    }
    switch err = sectionCtx1.Commit(); err {
    case error(nil):
      goto c
    case distsys.Aborted:
      goto c2
    default:
      return err
    }
  }
}

func AProducer(self0 distsys.TLAValue, constants1 Constants, net0 distsys.ArchetypeResource, s distsys.ArchetypeResource) error {
  var requester distsys.ArchetypeResource = distsys.NewLocalArchetypeResource(distsys.TLAValue{})
  var err0 error
  
  p: {
    sectionCtx2 := distsys.NewPCalSectionContext()
    var exprReads2 []distsys.TLAValue
    exprReads2, err0 = distsys.WhileCatchingPanics(func() distsys.TLAValue { return distsys.TLA_TRUE })
    if err0 != nil {
      sectionCtx2.Abort()
      if err0 == distsys.Aborted {
        goto p
      } else {
        return err0
      }
    }
    if exprReads2[0].IsTrue() {
      switch err0 = sectionCtx2.Commit(); err0 {
      case error(nil):
        goto p1
      case distsys.Aborted:
        goto p
      default:
        return err0
      }
    } else {
      // no statements
    }
    // no statements
  }
  p1: {
    sectionCtx3 := distsys.NewPCalSectionContext()
    var exprReads3 []distsys.TLAValue
    exprReads3, err0 = distsys.WhileCatchingPanics(func() distsys.TLAValue { return sectionCtx3.Read(net0, []distsys.TLAValue{self0}) })
    if err0 != nil {
      sectionCtx3.Abort()
      if err0 == distsys.Aborted {
        goto p1
      } else {
        return err0
      }
    }
    err0 = sectionCtx3.Write(requester, exprReads3[1:], exprReads3[0])
    if err0 != nil {
      sectionCtx3.Abort()
      if err0 == distsys.Aborted {
        goto p1
      } else {
        return err0
      }
    }
    switch err0 = sectionCtx3.Commit(); err0 {
    case error(nil):
      goto p2
    case distsys.Aborted:
      goto p1
    default:
      return err0
    }
  }
  p2: {
    sectionCtx4 := distsys.NewPCalSectionContext()
    var exprReads4 []distsys.TLAValue
    exprReads4, err0 = distsys.WhileCatchingPanics(func() distsys.TLAValue { return sectionCtx4.Read(s, []distsys.TLAValue{}) }, func() distsys.TLAValue { return sectionCtx4.Read(requester, []distsys.TLAValue{}) })
    if err0 != nil {
      sectionCtx4.Abort()
      if err0 == distsys.Aborted {
        goto p2
      } else {
        return err0
      }
    }
    err0 = sectionCtx4.Write(net0, exprReads4[1:], exprReads4[0])
    if err0 != nil {
      sectionCtx4.Abort()
      if err0 == distsys.Aborted {
        goto p2
      } else {
        return err0
      }
    }
    switch err0 = sectionCtx4.Commit(); err0 {
    case error(nil):
      goto p
    case distsys.Aborted:
      goto p2
    default:
      return err0
    }
  }
}

