package main

import (
	"time"

	"example.com/echo"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var addrs = map[int]string{
	1: "localhost:8000",
	2: "localhost:8001",
}

func getNetworkMaker(self tla.TLAValue) distsys.ArchetypeResourceMaker {
	return resources.RelaxedMailboxesMaker(
		func(index tla.TLAValue) (resources.TCPMailboxKind, string) {
			kind := resources.TCPMailboxesRemote
			if index.Equal(self) {
				kind = resources.TCPMailboxesLocal
			}
			return kind, addrs[int(index.AsNumber())]
		},
	)
}

func server() {
	self := tla.MakeTLANumber(1)
	ctx := distsys.NewMPCalContext(self, echo.AServer,
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self)),
	)
	defer ctx.Close()

	ctx.Run()
}

func client() {
	self := tla.MakeTLANumber(2)
	in := make(chan tla.TLAValue)
	out := make(chan tla.TLAValue)
	ctx := distsys.NewMPCalContext(self, echo.AClient,
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self)),
		distsys.EnsureArchetypeRefParam("in", resources.InputChannelMaker(in)),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(out)),
	)
	defer ctx.Close()

	go ctx.Run()

	echo.Benchmark(in, out)
}

func main() {
	go server()

	time.Sleep(1 * time.Second)

	client()
}
