package main

import (
	"fmt"
	"os"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/distcompiler/pgo/omnilink/porcupine/setbench"
)

func main() {
	if len(os.Args) < 3 {
		panic(fmt.Errorf("Too few command-line arguments, got: %v. Need mode then tracefile.", os.Args))
	}
	var err error
	mode, traceFile := os.Args[1], os.Args[2]
	var model porcupine.Model
	var ops []porcupine.Operation
	loadStartTime := time.Now()
	switch mode {
	case "setbench":
		ops, err = setbench.LoadOperations(traceFile)
		if err != nil {
			panic(err)
		}
		model = setbench.SetBenchModel
	default:
		panic(fmt.Errorf("Invalid mode %s. Options: setbench", mode))
	}
	loadEndTime := time.Now()
	fmt.Printf("Loaded %v operations in %v\n", len(ops), loadEndTime.Sub(loadStartTime))

	result, info := porcupine.CheckOperationsVerbose(model, ops, 0)
	checkEndTime := time.Now()
	fmt.Printf("Linearizability check result: %v in %v, writing path to ./viz.html\n", result, checkEndTime.Sub(loadEndTime))
	err = porcupine.VisualizePath(model, info, "./viz.html")
	if err != nil {
		panic(err)
	}

	if result != porcupine.Ok {
		os.Exit(1)
	}
}
