package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"

	"github.com/DistCompiler/pgo/systems/raftkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
	"github.com/dgraph-io/badger/v3"
	"github.com/pkg/profile"
)

func main() {
	var srvId int
	var configPath string
	var profileMode string
	flag.IntVar(&srvId, "srvId", -1, "Server ID")
	flag.StringVar(&configPath, "c", "", "Config file")
	flag.StringVar(&profileMode, "profile.mode", "", "enable profiling mode, one of [cpu, mem, mutex, block, goroutine, trace]")

	flag.Parse()

	if srvId == -1 {
		log.Fatal("srvId is not provided or it is invalid")
	}
	if configPath == "" {
		log.Fatal("config file is not provided")
	}
	if profileMode != "" {
		profilePath := filepath.Join("profiles", fmt.Sprintf("srv%d", srvId))

		switch profileMode {
		case "cpu":
			defer profile.Start(profile.CPUProfile, profile.ProfilePath(profilePath)).Stop()
		case "mem":
			defer profile.Start(profile.MemProfile, profile.ProfilePath(profilePath)).Stop()
		case "mutex":
			defer profile.Start(profile.MutexProfile, profile.ProfilePath(profilePath)).Stop()
		case "block":
			defer profile.Start(profile.BlockProfile, profile.ProfilePath(profilePath)).Stop()
		case "goroutine":
			defer profile.Start(profile.GoroutineProfile, profile.ProfilePath(profilePath)).Stop()
		case "trace":
			defer profile.Start(profile.TraceProfile, profile.ProfilePath(profilePath)).Stop()
		default:
			log.Fatal("invalid profile.mode value")
		}
	}

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	dbPath := fmt.Sprintf("/tmp/raftkvs/server%d/badger", srvId)

	// temp: removing existing badger files
	log.Println("removing badger files")
	if err := os.RemoveAll(dbPath); err != nil {
		log.Println(err)
	}

	log.Println("persist", c.Persist)

	var db *badger.DB
	if c.Persist {
		db, err = badger.Open(badger.DefaultOptions(dbPath))
		if err != nil {
			log.Fatal(err)
		}
		defer func() {
			if err := db.Close(); err != nil {
				log.Println(err)
			}
		}()
	}

	s := bootstrap.NewServer(srvId, c, db)

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

	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)

	<-sigCh
	log.Println("received SIGTERM")
}
