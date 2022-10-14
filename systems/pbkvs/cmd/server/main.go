package main

import (
	"flag"
	"log"
	"os"
	"os/signal"
	"syscall"

	"github.com/DistCompiler/pgo/systems/pbkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/pbkvs/configs"
)

func main() {
	var srvId int
	var configPath string
	flag.IntVar(&srvId, "srvId", -1, "Server ID")
	flag.StringVar(&configPath, "c", "", "Config file")

	flag.Parse()
	if srvId == -1 {
		log.Fatal("srvId is not provided or it is invalid")
	}
	if configPath == "" {
		log.Fatal("config file is not provided")
	}

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	r := bootstrap.NewReplica(srvId, c)
	go func() {
		err := r.Run()
		if err != nil {
			log.Println(err)
		}
	}()
	defer func() {
		err := r.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)

	<-sigCh
	log.Println("received SIGTERM")
}
