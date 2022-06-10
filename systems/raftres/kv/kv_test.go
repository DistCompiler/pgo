package kv_test

import (
	"fmt"
	"log"
	"sync"
	"testing"

	"github.com/DistCompiler/pgo/systems/raftres/configs"
	"github.com/DistCompiler/pgo/systems/raftres/kv"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
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

func broadcast(propCh chan tla.TLAValue, acctChans []chan tla.TLAValue) {
	iface := distsys.NewMPCalContextWithoutArchetype().IFace()

	for {
		m := <-propCh
		acceptedMsg := tla.MakeTLARecord([]tla.TLARecordField{
			{
				Key:   tla.MakeTLAString("mtype"),
				Value: kv.AcceptMessage(iface),
			},
			{
				Key:   tla.MakeTLAString("mcmd"),
				Value: m.ApplyFunction(tla.MakeTLAString("mcmd")),
			},
		})

		for _, acctCh := range acctChans {
			acctCh <- acceptedMsg
		}
	}
}

func assert(cond bool) {
	if !cond {
		panic("")
	}
}

const numRequestPairs = 10

func clientRun(c *kv.Client, reqCh chan kv.Request, respCh chan kv.Response, wg *sync.WaitGroup) {
	defer wg.Done()

	go func() {
		err := c.Run(reqCh, respCh)
		if err != nil {
			log.Println(err)
		}
	}()

	for i := 0; i < numRequestPairs; i++ {
		key := fmt.Sprintf("key%d", c.Id)
		value := fmt.Sprintf("value%d", i)

		{
			req := kv.PutRequest{
				Key:   key,
				Value: value,
			}
			reqCh <- req
			resp := <-respCh

			assert(resp.OK)
			assert(resp.Key == key && resp.Value == value)
		}

		{
			req := kv.GetRequest{
				Key: key,
			}
			reqCh <- req
			resp := <-respCh

			assert(resp.OK)
			assert(resp.Key == key && resp.Value == value)
		}
	}
}

func TestKV(t *testing.T) {
	c, err := configs.ReadConfig("../configs/local-3.yaml")
	if err != nil {
		t.Fatal(err)
	}

	var monitors []*resources.Monitor
	var servers []*kv.Server

	propCh := make(chan tla.TLAValue)
	var acctChans []chan tla.TLAValue
	{
		for srvId := range c.Servers {
			mon := setupMonitor(c, srvId)
			monitors = append(monitors, mon)

			acctCh := make(chan tla.TLAValue)
			acctChans = append(acctChans, acctCh)

			s := kv.NewServer(srvId, c, mon, propCh, acctCh)
			servers = append(servers, s)

			go func() {
				err := s.Run()
				if err != nil {
					log.Println(err)
				}
			}()
		}
		go broadcast(propCh, acctChans)
	}

	var clients []*kv.Client
	var reqChs []chan kv.Request
	var respChs []chan kv.Response
	var wg sync.WaitGroup
	{
		wg.Add(c.NumClients)
		for clientId := range c.Clients {
			c := kv.NewClient(clientId, c)
			clients = append(clients, c)

			reqCh := make(chan kv.Request)
			reqChs = append(reqChs, reqCh)

			respCh := make(chan kv.Response)
			respChs = append(respChs, respCh)

			go clientRun(c, reqCh, respCh, &wg)
		}
	}

	wg.Wait()
	log.Println("clients done")

	{
		for i := range clients {
			close(reqChs[i])
			close(respChs[i])
			err := clients[i].Close()
			if err != nil {
				log.Println(err)
			}
		}
		for i := range servers {
			servers[i].Close()
			monitors[i].Close()
		}
	}
}
