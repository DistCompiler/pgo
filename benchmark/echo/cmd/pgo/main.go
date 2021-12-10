package main

import (
	"flag"
	"log"
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

type mailboxMaker func(fn resources.MailboxesAddressMappingFn) distsys.ArchetypeResourceMaker

func getNetworkMaker(self tla.TLAValue, maker mailboxMaker) distsys.ArchetypeResourceMaker {
	return maker(
		func(index tla.TLAValue) (resources.MailboxKind, string) {
			kind := resources.MailboxesRemote
			if index.Equal(self) {
				kind = resources.MailboxesLocal
			}
			return kind, addrs[int(index.AsNumber())]
		},
	)
}

func server(netMaker mailboxMaker) {
	self := tla.MakeTLANumber(1)
	ctx := distsys.NewMPCalContext(self, echo.AServer,
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, netMaker)),
	)
	defer ctx.Stop()

	ctx.Run()
}

func client(netMaker mailboxMaker) {
	self := tla.MakeTLANumber(2)
	in := make(chan tla.TLAValue)
	out := make(chan tla.TLAValue)
	ctx := distsys.NewMPCalContext(self, echo.AClient,
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, netMaker)),
		distsys.EnsureArchetypeRefParam("in", resources.InputChannelMaker(in)),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(out)),
	)
	defer ctx.Stop()

	go ctx.Run()

	echo.Benchmark(in, out)
}

func main() {
	var netMaker mailboxMaker

	var mbox string
	flag.StringVar(&mbox, "mbox", "", "mailboxes to use")
	flag.Parse()

	switch mbox {
	case "tcp":
		netMaker = resources.TCPMailboxesMaker
	case "relaxed":
		netMaker = resources.RelaxedMailboxesMaker
	default:
		log.Fatal("invalid mbox option")
	}

	go server(netMaker)

	time.Sleep(1 * time.Second)

	client(netMaker)
}
