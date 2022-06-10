package raftres_test

import (
	"fmt"
	"log"
	"sync"
	"testing"
	"time"

	"github.com/DistCompiler/pgo/systems/raftres"
	"github.com/DistCompiler/pgo/systems/raftres/configs"
	"github.com/DistCompiler/pgo/systems/raftres/kv"
)

func assert(cond bool) {
	if !cond {
		panic("")
	}
}

const numRequestPairs = 20

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

			fmt.Println(req)
			fmt.Println(resp)

			assert(resp.OK)
			assert(resp.Key == key && resp.Value == value)
		}

		{
			req := kv.GetRequest{
				Key: key,
			}
			reqCh <- req
			resp := <-respCh

			fmt.Println(req)
			fmt.Println(resp)

			assert(resp.OK)
			assert(resp.Key == key && resp.Value == value)
		}
	}

}

func TestRaftResource(t *testing.T) {
	c, err := configs.ReadConfig("configs/local-3.yaml")
	if err != nil {
		t.Fatal(err)
	}

	var servers []*raftres.Server
	{
		for srvId := range c.Servers {
			s := raftres.NewServer(srvId, c)
			servers = append(servers, s)

			go func() {
				err := s.Run()
				if err != nil {
					log.Println(err)
				}
			}()
		}
	}

	time.Sleep(2 * time.Second)
	log.Println("starting clients")

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
		for i := range servers {
			err := servers[i].Close()
			if err != nil {
				log.Println(err)
			}
		}
		for i := range clients {
			close(reqChs[i])
			close(respChs[i])
			err := clients[i].Close()
			if err != nil {
				log.Println(err)
			}
		}
	}
}
