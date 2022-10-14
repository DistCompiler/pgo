package pbkvs_test

import (
	"fmt"
	"log"
	"sync"
	"testing"

	"github.com/DistCompiler/pgo/systems/pbkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/pbkvs/configs"
)

func TestPBKVS_OneReplicaOneClient(t *testing.T) {
	bootstrap.ResetClientFailureDetector()

	c, err := configs.ReadConfig("configs/local-1-1.yaml")
	if err != nil {
		t.Fatal(err)
	}

	replica := bootstrap.NewReplica(1, c)
	go func() {
		err := replica.Run()
		if err != nil {
			log.Println(err)
		}
	}()
	defer replica.Close()

	client := bootstrap.NewClient(1, c)
	go func() {
		err := client.Run()
		if err != nil {
			log.Println(err)
		}
	}()
	defer client.Close()

	_, err = client.Put("key1", "value1")
	if err != nil {
		t.Fatal(err)
	}

	resp, err := client.Get("key1")
	if err != nil {
		t.Fatal(err)
	}
	if resp != "value1" {
		t.Fatal("wrong response")
	}

	resp3, err := client.Get("key2")
	log.Println(resp3, err)
}

func clientRun(client *bootstrap.Client, wg *sync.WaitGroup) error {
	defer wg.Done()

	numRequests := 15
	for i := 0; i < numRequests; i++ {
		key := fmt.Sprintf("key%d", i)
		value := fmt.Sprintf("value%d", i)

		_, err := client.Put(key, value)
		if err != nil {
			return err
		}
	}
	return nil
}

func TestPBKVS_ThreeReplicasThreeClients(t *testing.T) {
	bootstrap.ResetClientFailureDetector()

	c, err := configs.ReadConfig("configs/local-3-3.yaml")
	if err != nil {
		t.Fatal(err)
	}

	for replicaId := range c.Replicas {
		replica := bootstrap.NewReplica(replicaId, c)
		go func() {
			err := replica.Run()
			if err != nil {
				log.Println(err)
			}
		}()
		defer replica.Close()
	}

	var wg sync.WaitGroup
	for clientId := range c.Clients {
		client := bootstrap.NewClient(clientId, c)
		go func() {
			err := client.Run()
			if err != nil {
				log.Println(err)
			}
		}()
		wg.Add(1)
		go func() {
			err := clientRun(client, &wg)
			if err != nil {
				panic(err)
			}
		}()
		defer client.Close()
	}
	wg.Wait()
}
