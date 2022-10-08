package raftres

import (
	"fmt"
	"log"
	"os"

	"github.com/DistCompiler/pgo/systems/raftres/configs"
	"github.com/DistCompiler/pgo/systems/raftres/kv"
	"github.com/DistCompiler/pgo/systems/raftres/raft/bootstrap"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/dgraph-io/badger/v3"
	"go.uber.org/multierr"
)

type Server struct {
	Id     int
	Config configs.Root

	db  *badger.DB
	mon *resources.Monitor

	raft *bootstrap.Server
	kv   *kv.Server
}

func NewServer(srvId int, c configs.Root) *Server {
	acctCh := make(chan tla.TLAValue, 100)
	propCh := make(chan tla.TLAValue, 100)

	dbPath := fmt.Sprintf("/tmp/raftres/server%d/badger", srvId)

	// temp: removing existing badger files
	log.Println("removing badger files")
	if err := os.RemoveAll(dbPath); err != nil {
		log.Println(err)
	}

	db, err := badger.Open(badger.DefaultOptions(dbPath))
	if err != nil {
		log.Fatal(err)
	}

	mon := resources.NewMonitor(c.Servers[srvId].MonitorAddr)

	raft := bootstrap.NewServer(srvId, c, db, mon, propCh, acctCh)
	kvServer := kv.NewServer(srvId, c, mon, propCh, acctCh)

	return &Server{
		Id:     srvId,
		Config: c,
		db:     db,
		mon:    mon,
		raft:   raft,
		kv:     kvServer,
	}
}

func (s *Server) Run() error {
	cnt := 3

	errCh := make(chan error)
	go func() {
		err := s.mon.ListenAndServe()
		errCh <- err
	}()
	go func() {
		err := s.raft.Run()
		errCh <- err
	}()
	go func() {
		err := s.kv.Run()
		errCh <- err
	}()

	for i := 0; i < cnt; i++ {
		err := <-errCh
		if err != nil {
			return err
		}
	}
	return nil
}

func (s *Server) Close() error {
	var err error

	err = multierr.Append(err, s.raft.Close())
	err = multierr.Append(err, s.kv.Close())
	err = multierr.Append(err, s.mon.Close())
	err = multierr.Append(err, s.db.Close())
	return err
}
