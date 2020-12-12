package main

import (
	"fmt"
	"load_balancer"
	"os"
	"io/ioutil"
	"math/rand"
	"pgo/distsys"
	"strconv"
	//"strings"
)

var configuration map[string]string
var id string
var role string
var selfStr string
var connections *distsys.Connections
var barrier *distsys.SyncBarrier

const (
	MAILBOX_SIZE = 10
	CLIENT_COUNT = 1
	REQUEST_COUNT = 100
)

func init() {
	if len(os.Args) < 3 {
		fmt.Printf("Usage: %s processName(processArgument) ip:port\n", os.Args[0])
	}

	id = os.Args[1]
	ipPort := os.Args[2]
	configuration = map[string]string{
		"ALoadBalancer(0)": "127.0.0.1:2222",
		"AServer(1)":       "127.0.0.1:3333",
		"AServer(2)":       "127.0.0.1:4444",
		"AServer(3)":       "127.0.0.1:5555",
	}
	for i := 0; i < CLIENT_COUNT; i++ {
	    configuration[fmt.Sprintf("AClient(%d)", i+4)] = fmt.Sprintf("127.0.0.1:%d", 6000+i)
	}

	if _, ok := configuration[id]; !ok {
		fmt.Fprintf(os.Stderr, "Unknown process: %s\n", id)
		os.Exit(1)
	}

	role, selfStr = distsys.ParseProcessId(id)
	coordinator := configuration["ALoadBalancer(0)"]
	connections = distsys.NewConnections(ipPort)
	barrier = distsys.NewSyncBarrier(configuration, connections, ipPort, coordinator)
}

func makeMailboxRef(name string) *distsys.Mailbox {
	mbox, err := distsys.MailboxRef(name, 0, connections, configuration, []string{id}, MAILBOX_SIZE, 0)
	if err != nil {
		panic(err)
	}

	return mbox
}

func waitBarrier() {
	if err := barrier.WaitPeers(); err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(1)
	}
}

func main() {
	mailboxes := []distsys.ArchetypeResource{}
	mailboxes = append(mailboxes, makeMailboxRef("ALoadBalancer(0)"))

	for i := 1; i <= load_balancer.NUM_SERVERS; i++ {
		mailboxes = append(mailboxes, makeMailboxRef(fmt.Sprintf("AServer(%d)", i)))
	}

	for i := load_balancer.NUM_SERVERS + 1; i <= load_balancer.NUM_SERVERS+load_balancer.NUM_CLIENTS; i++ {
		mailboxes = append(mailboxes, makeMailboxRef(fmt.Sprintf("AClient(%d)", i)))
	}

	self, err := strconv.Atoi(selfStr)
	if err != nil {
		panic(err)
	}

	// wait for all process to come online
	waitBarrier()

	if role == "ALoadBalancer" {
		go load_balancer.ALoadBalancer(self, distsys.ArchetypeResourceSlice(mailboxes))
	} else if role == "AServer" {
		path := os.Args[3]
		fs := distsys.NewFileSystemDirectory(path)

		go load_balancer.AServer(self, distsys.ArchetypeResourceSlice(mailboxes), fs)
	} else {
		fmt.Printf("Connected!\n")

		in := distsys.NewLocalChannel("in", 0)
		out := distsys.NewLocalChannel("out", 0)

		go load_balancer.AClient(self, distsys.ArchetypeResourceSlice(mailboxes), in, out)

		paths, err := ioutil.ReadDir("pages")
		if err != nil {
		    panic(err)
		}

		for i := 0; i < REQUEST_COUNT; i++ {
		    path := paths[rand.Intn(len(paths))]
			in.Send(path.Name())
			_ = out.Receive().([]byte)
			// we're not measuring printf performance here...
			//fmt.Printf("Received page %s: %s\n", path.Name(), strings.TrimSpace(string(bArray[:len(bArray)])))
			//fmt.Printf("Client %d received page %s\n", self-4, path.Name())
		}
		//fmt.Printf("Client %d done\n", self-4)
	}

	// Wait for all peers to disconnect
	waitBarrier()
}
