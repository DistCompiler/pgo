package main

import (
	"flag"
	"fmt"
	"log"

	"example.org/raftkvs/configs"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/dgraph-io/badger/v3"
)

func main() {
	var srvIdInt int
	flag.IntVar(&srvIdInt, "srvId", -1, "Server ID")

	flag.Parse()

	if srvIdInt == -1 {
		log.Fatal("srvId is not provided or it is invalid")
	}
	srvId := tla.MakeTLANumber(int32(srvIdInt))

	c, err := configs.ReadConfig()
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

	mon := setupMonitor(srvId, c)

	ctxs := newServerCtxs(srvId, c, db)
	for i := range ctxs {
		ctx := ctxs[i]
		go func() {
			err := mon.RunArchetype(ctx)
			log.Printf("archetype %v finished, err = %v", ctx.IFace().Self(), err)
		}()
	}

	select {}
}
