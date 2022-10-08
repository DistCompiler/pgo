package main

import (
	"flag"
	"log"
	"os"
	"os/signal"
	"syscall"

	"github.com/DistCompiler/pgo/systems/raftres"
	"github.com/DistCompiler/pgo/systems/raftres/configs"
)

func main() {
	var srvId int
	var configPath string
	flag.IntVar(&srvId, "srvId", -1, "Server ID")
	flag.StringVar(&configPath, "c", "", "Config file")

	flag.Parse()

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	s := raftres.NewServer(srvId, c)

	go func() {
		err := s.Run()
		if err != nil {
			log.Println(err)
		}
	}()

	defer func() {
		err := s.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	sigCh := make(chan os.Signal)
	signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)
	select {
	case <-sigCh:
		log.Println("received SIGTERM")
	}
}
