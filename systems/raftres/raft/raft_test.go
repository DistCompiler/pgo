package raft_test

import (
	"fmt"
	"log"
	"testing"
	"time"

	"github.com/DistCompiler/pgo/systems/raftres/configs"
	"github.com/DistCompiler/pgo/systems/raftres/raft/bootstrap"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/dgraph-io/badger/v3"
)

func setupMonitor(c configs.Root, srvId int) *resources.Monitor {
	addr := c.Servers[srvId].MonitorAddr
	mon := resources.NewMonitor(addr)
	go func() {
		if err := mon.ListenAndServe(); err != nil {
			log.Fatal(err)
		}
	}()
	return mon
}

func TestRaftLeaderElection(t *testing.T) {
	c, err := configs.ReadConfig("../configs/local-3.yaml")
	if err != nil {
		t.Fatal(err)
	}

	var monitors []*resources.Monitor
	var servers []*bootstrap.Server

	for id := range c.Servers {
		dbPath := fmt.Sprintf("/tmp/server%d/badger", id)
		db, err := badger.Open(badger.DefaultOptions(dbPath))
		if err != nil {
			log.Fatal(err)
		}
		defer func() {
			if err := db.Close(); err != nil {
				log.Println(err)
			}
		}()

		mon := setupMonitor(c, id)
		monitors = append(monitors, mon)

		propCh := make(chan tla.TLAValue, 10)
		acctCh := make(chan tla.TLAValue, 10)

		s := bootstrap.NewServer(id, c, db, mon, propCh, acctCh)
		servers = append(servers, s)
		go func() {
			err := s.Run()
			if err != nil {
				log.Println(err)
			}
		}()
	}

	time.Sleep(2 * time.Second)

	for _, s := range servers {
		err := s.Close()
		if err != nil {
			t.Error(err)
		}
	}
	for _, mon := range monitors {
		err := mon.Close()
		if err != nil {
			t.Error(err)
		}
	}
}
