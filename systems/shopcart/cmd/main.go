package main

import (
	"flag"
	"fmt"
	"log"
	"time"

	"github.com/DistCompiler/pgo/systems/shopcart"
	"github.com/DistCompiler/pgo/systems/shopcart/configs"
)

func main() {
	var nid int
	var configPath string
	flag.IntVar(&nid, "nid", -1, "Server ID")
	flag.StringVar(&configPath, "c", "", "Config file")

	flag.Parse()

	if nid == -1 {
		log.Fatal("id is not provided or it is invalid")
	}
	if configPath == "" {
		log.Fatal("config file is not provided")
	}

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	ch := make(chan shopcart.Event, 10)
	node := shopcart.NewNode(nid, c, ch)
	go func() {
		if err := node.Run(); err != nil {
			log.Println(err)
		}
	}()

	var start time.Time
	roundIdx := 0
	numEvents := 2 * c.NumRounds
	for i := 0; i < numEvents; i++ {
		e := <-ch

		// log.Println(nid, e)

		if e == shopcart.AddStartEvent {
			start = time.Now()
		} else if e == shopcart.AddFinishEvent {
			elapsed := time.Since(start)
			fmt.Println("RESULT", roundIdx, nid, elapsed)
			roundIdx += 1
		}
	}

	if err := node.Close(); err != nil {
		log.Println(err)
	}
}
