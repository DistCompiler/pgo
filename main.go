package main

import (
	"fmt"
	"time"
	"load_balancer" // import the compiled load_balancer.tla module
	"os"
	"pgo/distsys"
	"strconv"
	"strings"
)

var configuration map[string]string
var id string
var role string
var selfStr string
var connections *distsys.Connections
var barrier *distsys.SyncBarrier

const (
	MAILBOX_SIZE = 10
)

func init() {
	if len(os.Args) < 3 {
		fmt.Printf("Usage: %s processName(processArgument) ip:port\n", os.Args[0])
	}

	id = os.Args[1]
	ipPort := os.Args[2]
        // the assumed mapping of Process(id) to host:port
	configuration = map[string]string{
		"ALoadBalancer(0)": "tlaconf-aloadbalancer0:2222",
		"AServer(1)":       "tlaconf-aserver1:3333",
		"AServer(2)":       "tlaconf-aserver2:4444",
		"AClient(3)":       "tlaconf-aclient3:5555",
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
	fmt.Printf("Waiting for peers...\n")
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

        // depending on which process we are, run the corresponding archetype in a goroutine
        // pass in relevant resources, generally at least the mailboxes
	if role == "ALoadBalancer" {
		go load_balancer.ALoadBalancer(self, distsys.ArchetypeResourceSlice(mailboxes))
		fmt.Printf("Launched load balancer\n")
	} else if role == "AServer" {
                // provide the servers with a directory to serve (path is a command-line argument)
		path := os.Args[3]
		fs := distsys.NewFileSystemDirectory(path)

		go load_balancer.AServer(self, distsys.ArchetypeResourceSlice(mailboxes), fs)
		fmt.Printf("Launched server\n")
	} else {
		fmt.Printf("Connected!\n")

                // these resources control the client. requests go to in, and responses can be read from out
		in := distsys.NewLocalChannel("in", 0)
		out := distsys.NewLocalChannel("out", 0)

		go load_balancer.AClient(self, distsys.ArchetypeResourceSlice(mailboxes), in, out)

                // keep requesting each page one by one forever
		paths := []string{"page1.html", "page1.html", "page2.html"}
                for i := 0;; i++ {
                        path := paths[i % 3];
			fmt.Printf("Requesting page %s\n", path)
			in.Send(path)
			bArray := out.Receive().([]byte)
			fmt.Printf("Received page: %s\n", strings.TrimSpace(string(bArray[:len(bArray)])))
			fmt.Printf("(waiting one second for demo)\n")
			time.Sleep(5 * time.Second)
		}
	}

	// Wait for all peers to disconnect
	waitBarrier()
}
