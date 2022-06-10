package raftres

import (
	"fmt"
	"log"

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

	dbPath := fmt.Sprintf("/tmp/server%d/badger", srvId)
	db, err := badger.Open(badger.DefaultOptions(dbPath))
	if err != nil {
		log.Fatal(err)
	}

	mon := resources.NewMonitor(c.Servers[srvId].MonitorAddr)

	raft := bootstrap.NewServer(srvId, c, db, mon, propCh, acctCh)
	kv := kv.NewServer(srvId, c, mon, propCh, acctCh)

	return &Server{
		Id:     srvId,
		Config: c,
		db:     db,
		mon:    mon,
		raft:   raft,
		kv:     kv,
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
	var cerr error

	cerr = multierr.Append(cerr, s.raft.Close())
	cerr = multierr.Append(cerr, s.kv.Close())
	cerr = multierr.Append(cerr, s.mon.Close())
	return cerr
}
