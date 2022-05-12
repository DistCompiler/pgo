package main

import (
	"flag"
	"fmt"
	"log"

	"github.com/DistCompiler/pgo/systems/raftkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
	"github.com/dgraph-io/badger/v3"
)

func main() {
	var srvIdInt int
	var configPath string
	flag.IntVar(&srvIdInt, "srvId", -1, "Server ID")
	flag.StringVar(&configPath, "c", "", "Config file")

	flag.Parse()

	if srvIdInt == -1 {
		log.Fatal("srvId is not provided or it is invalid")
	}
	if configPath == "" {
		log.Fatal("config file is not provided")
	}

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	dbPath := fmt.Sprintf("/tmp/server%d/badger", srvIdInt)
	db, err := badger.Open(badger.DefaultOptions(dbPath))
	if err != nil {
		log.Fatal(err)
	}
	defer func() {
		if err := db.Close(); err != nil {
			log.Println(err)
		}
	}()

	s := bootstrap.NewServer(srvIdInt, c, db)

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

	select {}
}
