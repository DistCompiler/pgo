package main

import (
	"fmt"
	"os"
	"pgo/distsys"
	"strconv"
)

var iters int

var procs int

var counter int

var processName string

var processArgument string

var err error

var globalState *distsys.StateServer

var refs distsys.VarReferences

func init() {
	iters = 10
	procs = 3
	counter = 0
	if len(os.Args) != 3 {
		fmt.Printf("Usage: %s processName(processArgument) ip:port\n", os.Args[0])
		os.Exit(1)
	}
	processPlusArgument := os.Args[1]
	ipPort := os.Args[2]
	processName, processArgument = distsys.ParseProcessId(processPlusArgument)
	peers := []string{"10.0.0.1:1111", "10.0.0.2:2222", "10.0.0.3:3333"}
	coordinator := peers[0]
	globalState, err = distsys.NewStateServer(peers, ipPort, coordinator, map[string]interface{}{
		"counter": counter,
	}, distsys.NewRandomMigrate(ipPort))
	if err != nil {
		panic(err)
	}
}

func P(self int) {
	i := 0
	for {
		if !(i < iters) {
			break
		}
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"counter"}})
		if err != nil {
			panic(err)
		}
		counter = refs.Get("counter").(int)
		counter = counter + 1
		fmt.Printf("%v\n", counter)
		refs.Set("counter", counter)
		err = globalState.Release(refs)
		if err != nil {
			panic(err)
		}
		i = i + 1
	}
}

func main() {
	err = globalState.WaitPeers()
	if err != nil {
		panic(err)
	}
	switch processName {
	case "P":
		i, err0 := strconv.Atoi(processArgument)
		if err0 != nil {
			panic("Process P requires an integer argument; err = " + err0.Error())
		}
		P(i)
	default:
		panic("Unknown process " + processName)
	}
	err = globalState.WaitPeers()
	if err != nil {
		panic(err)
	}
}
