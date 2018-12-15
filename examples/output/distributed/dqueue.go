package main

import (
	"fmt"
	"os"
	"pgo/distsys"
	"strconv"
)

var queue []string

var processName string

var processArgument string

var err error

var globalState *distsys.StateServer

var refs distsys.VarReferences

func init() {
	queue = []string{}
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
		"queue": queue,
	}, distsys.NewRandomMigrate(ipPort))
	if err != nil {
		panic(err)
	}
}

func Producer(self int) {
	for {
		if !true {
			break
		}
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"queue"}})
		if err != nil {
			panic(err)
		}
		queue = refs.Get("queue").([]string)
		if len(queue) < 3 {
			tmpSlice := make([]string, len(queue), len(queue)+1)
			copy(tmpSlice, queue)
			tmpSlice = append(tmpSlice, "resource")
			queue = tmpSlice
		}
		refs.Set("queue", queue)
		err = globalState.Release(refs)
		if err != nil {
			panic(err)
		}
	}
}

func Consumer(self int) {
	resource := ""
	for {
		if !true {
			break
		}
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"queue"}})
		if err != nil {
			panic(err)
		}
		queue = refs.Get("queue").([]string)
		if len(queue) != 0 {
			resource = queue[0]
			queue = queue[1:]
			if !(resource == "resource") {
				panic("(resource)=(\"resource\")")
			}
			fmt.Printf("%v\n", resource)
		}
		refs.Set("queue", queue)
		err = globalState.Release(refs)
		if err != nil {
			panic(err)
		}
	}
}

func main() {
	err = globalState.WaitPeers()
	if err != nil {
		panic(err)
	}
	switch processName {
	case "Producer":
		i, err0 := strconv.Atoi(processArgument)
		if err0 != nil {
			panic("Process Producer requires an integer argument; err = " + err0.Error())
		}
		Producer(i)
	case "Consumer":
		i, err0 := strconv.Atoi(processArgument)
		if err0 != nil {
			panic("Process Consumer requires an integer argument; err = " + err0.Error())
		}
		Consumer(i)
	default:
		panic("Unknown process " + processName)
	}
	err = globalState.WaitPeers()
	if err != nil {
		panic(err)
	}
}
