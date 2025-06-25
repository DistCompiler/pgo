package raftkvs_test

import (
	"fmt"
	"log"
	"math/rand"
	"sync"
	"testing"
	"time"

	"github.com/DistCompiler/pgo/systems/raftkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
	"github.com/dgraph-io/badger/v3"
)

func getRequestKey(req bootstrap.Request) string {
	switch t := req.(type) {
	case bootstrap.GetRequest:
		return t.Key
	case bootstrap.PutRequest:
		return t.Key
	default:
		return "unknown"
	}
}

func checkResp(t *testing.T, resp bootstrap.Response, j int, reqs []bootstrap.Request) {
	reqKey := getRequestKey(reqs[j])
	if resp.Key != reqKey {
		t.Fatalf("wrong response key, expected: %v, got: %v", reqKey, resp.Key)
	}
	if resp.Type() == bootstrap.GetResponseType {
		reqValue := reqs[j-1].(bootstrap.PutRequest).Value
		if resp.Value != reqValue {
			t.Fatalf("wrong response value, expected: %v, got: %v", reqValue, resp.Value)
		}
	} else if resp.Type() == bootstrap.PutResponseType {
		reqValue := reqs[j].(bootstrap.PutRequest).Value
		if resp.Value != reqValue {
			t.Fatalf("wrong response value, expected: %v, got: %v", reqValue, resp.Value)
		}
	}
}

func runSafetyTest(t *testing.T, configPath string, numNodeFail int) {
	fmt.Printf("Testing %s\n", configPath)
	bootstrap.ResetClientFailureDetector()

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	var servers []*bootstrap.Server
	for id := range c.Servers {
		var db *badger.DB
		if c.Persist {
			dbPath := fmt.Sprintf("/tmp/server%d/badger", id)
			db, err = badger.Open(badger.DefaultOptions(dbPath))
			if err != nil {
				log.Fatal(err)
			}
			defer func() {
				if err := db.Close(); err != nil {
					t.Errorf("db close error %v", err)
				}
			}()
		}

		s := bootstrap.NewServer(id, c, db)
		servers = append(servers, s)
		defer func() {
			err := s.Close()
			if err != nil {
				t.Errorf("error closing server %d: %v", s.Id, err)
			} else {
				log.Printf("cleanup: server %d closed", s.Id)
			}
		}()

		go func() {
			err := s.Run()
			if err != nil {
				t.Errorf("error running server: %v", err)
			}
		}()
	}

	numRequestPairs := 10
	numRequests := numRequestPairs * 2

	delay := 3 * time.Second
	log.Printf("waiting %v", delay)
	time.Sleep(delay)

	failCh := make(chan struct{})

	if numNodeFail > 0 {
		go func() {
			d := rand.Intn(3500)
			time.Sleep(time.Duration(d) * time.Millisecond)
			for i := range numNodeFail {
				err := servers[i].Close()
				if err != nil {
					t.Errorf("error killing server %d: %v", i, err)
				} else {
					log.Printf("server %d crashed", servers[i].Id)
				}
			}
			failCh <- struct{}{}
		}()
	}

	reqCh := make(chan bootstrap.Request, numRequests)
	respCh := make(chan bootstrap.Response, numRequests)
	for clientId := range c.Clients {
		cl := bootstrap.NewClient(clientId, c)
		go func() {
			err := cl.Run(reqCh, respCh)
			if err != nil {
				t.Errorf("client run failed with error %v", err)
			}
		}()
		defer func() {
			err := cl.Close()
			if err != nil {
				t.Errorf("client closed with error %v", err)
			} else {
				log.Printf("cleanup: client %d closed", cl.Id)
			}
		}()
	}

	log.Println("sending client requests")
	keys := []string{"key1", "key2", "key3"}
	var reqs []bootstrap.Request
	for i := range numRequestPairs {
		key := keys[i%len(keys)]
		value := fmt.Sprintf("value%d", i)
		putReq := bootstrap.PutRequest{Key: key, Value: value}
		reqCh <- putReq
		reqs = append(reqs, putReq)

		getReq := bootstrap.GetRequest{Key: key}
		reqCh <- getReq
		reqs = append(reqs, getReq)
	}

	log.Printf("numRequests = %d", numRequests)

	for i := range numRequests {
		resp := <-respCh
		log.Printf("test received resp: %v", resp)
		checkResp(t, resp, i, reqs)
	}

	if numNodeFail > 0 {
		<-failCh
	}
}

func assert(t *testing.T, cond bool) {
	if !cond {
		t.Fatal("assertion failed!")
	}
}

func clientRun(t *testing.T, c *bootstrap.Client, wg *sync.WaitGroup) {
	const numRequests = 50

	defer wg.Done()

	reqCh := make(chan bootstrap.Request)
	respCh := make(chan bootstrap.Response)

	go func() {
		err := c.Run(reqCh, respCh)
		if err != nil {
			log.Println(err)
		}
	}()
	defer func() {
		close(reqCh)
		close(respCh)
	}()

	for i := range numRequests {
		key := fmt.Sprintf("key%d", c.Id)
		value := fmt.Sprintf("value%d", i)

		req := bootstrap.PutRequest{Key: key, Value: value}
		reqCh <- req

		resp := <-respCh

		assert(t, resp.OK)
		assert(t, resp.Key == key && resp.Value == value)
	}
}

func runLivenessTest(t *testing.T, configPath string) {
	bootstrap.ResetClientFailureDetector()

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	var servers []*bootstrap.Server
	for id := range c.Servers {
		var db *badger.DB
		if c.Persist {
			dbPath := fmt.Sprintf("/tmp/server%d/badger", id)
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

		s := bootstrap.NewServer(id, c, db)
		servers = append(servers, s)

		go func() {
			err := s.Run()
			if err != nil {
				log.Println(err)
			}
		}()
	}

	var wg sync.WaitGroup
	var clients []*bootstrap.Client
	for clientId := range c.Clients {
		cl := bootstrap.NewClient(clientId, c)
		clients = append(clients, cl)
		go clientRun(t, cl, &wg)
	}

	wg.Wait()

	{
		for i := range servers {
			err := servers[i].Close()
			if err != nil {
				log.Println(err)
			}
		}
		for i := range clients {
			err := clients[i].Close()
			if err != nil {
				log.Println(err)
			}
		}
	}
}

func TestSafety_OneServer(t *testing.T) {
	runSafetyTest(t, "configs/test-1-1.yaml", 0)
}

func TestSafety_TwoServers(t *testing.T) {
	runSafetyTest(t, "configs/test-2-1.yaml", 0)
}

func TestSafety_ThreeServers(t *testing.T) {
	runSafetyTest(t, "configs/test-3-1.yaml", 0)
}

func TestSafety_FourServers(t *testing.T) {
	runSafetyTest(t, "configs/test-4-1.yaml", 0)
}

func TestSafety_FiveServers(t *testing.T) {
	runSafetyTest(t, "configs/test-5-1.yaml", 0)
}

func TestSafety_OneFailing_ThreeServers(t *testing.T) {
	runSafetyTest(t, "configs/test-3-1.yaml", 1)
}

//func TestSafety_OneFailing_FiveServers(t *testing.T) {
//	runSafetyTest(t, "configs/test-5-1.yaml", 1)
//}

//func TestSafety_TwoFailing_FiveServers(t *testing.T) {
//	runSafetyTest(t, "configs/test-5-1.yaml", 2)
//}

// func TestLiveness_ThreeServers_ThreeClients(t *testing.T) {
// 	runLivenessTest(t, "configs/test-3-3.yaml")
// }

//func TestLiveness_ThreeServers_FiveClients(t *testing.T) {
//	runLivenessTest(t, "configs/test-3-5.yaml")
//}
