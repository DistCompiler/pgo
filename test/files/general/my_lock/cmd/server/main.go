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
	iface := distsys.NewMPCalContextWithoutArchetype().IFace()

	network := resources.NewTCPMailboxes(
		func(index tla.TLAValue) (resources.MailboxKind, string) {
			kind := resources.MailboxesRemote
			if index.Equal(my_lock.ServerID(iface)) {
				kind = resources.MailboxesLocal
			}
			addr := networkAddrs[int(index.AsNumber())]
			return kind, addr
		},
	)

	ctx := distsys.NewMPCalContext(my_lock.ServerID(iface), my_lock.AServer,
		distsys.EnsureArchetypeRefParam("network", network))

	ctx.Run()
}
