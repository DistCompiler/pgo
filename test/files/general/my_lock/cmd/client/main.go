package main

import (
	"example.com/my_lock"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var networkAddrs = map[int]string{
	0: "localhost:8000",
	1: "localhost:8001",
	2: "localhost:8002",
}

func main() {
	network := resources.NewTCPMailboxes(
		func(index tla.TLAValue) (resources.MailboxKind, string) {
			kind := resources.MailboxesRemote
			if index.Equal(tla.MakeTLANumber(0)) {
				kind = resources.MailboxesLocal
			}
			addr := networkAddrs[int(index.AsNumber())]
			return kind, addr
		},
	)
	ctx := distsys.NewMPCalContext(tla.MakeTLANumber(0), my_lock.AClient,
		distsys.EnsureArchetypeRefParam("network", network))
	ctx.Run()
}
