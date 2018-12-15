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

var token int

var processName string

var processArgument string

var err error

var globalState *distsys.StateServer

var refs distsys.VarReferences

func init() {
	iters = 10
	procs = 3
	counter = 0
	token = -1
	if len(os.Args) != 3 {
		fmt.Printf("Usage: %s processName(processArgument) ip:port\n", os.Args[0])
		os.Exit(1)
	}
	processPlusArgument := os.Args[1]
	ipPort := os.Args[2]
	processName, processArgument = distsys.ParseProcessId(processPlusArgument)
	peers := []string{"10.0.0.1:12345", "10.0.0.2:12345"}
	coordinator := peers[0]
	globalState, err = distsys.NewStateServer(peers, ipPort, coordinator, map[string]interface{}{
		"counter": counter,
		"token":   token,
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
	waitToken:
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"counter", "token"}})
		if err != nil {
			panic(err)
		}
		counter = refs.Get("counter").(int)
		token = refs.Get("token").(int)
		if !(token == -1 || token == self) {
			err = globalState.Release(refs)
			if err != nil {
				panic(err)
			}
			goto waitToken
		}
		refs.Set("counter", counter)
		refs.Set("token", token)
		err = globalState.Release(refs)
		if err != nil {
			panic(err)
		}
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"counter", "token"}})
		if err != nil {
			panic(err)
		}
		counter = refs.Get("counter").(int)
		token = refs.Get("token").(int)
		counter = counter + 1
		token = (self + 1) % procs
		fmt.Printf("%v\n", counter)
		refs.Set("counter", counter)
		refs.Set("token", token)
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
