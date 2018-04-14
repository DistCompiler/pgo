package distsys

import (
	"encoding/gob"
	"log"
	"net/rpc"
	"time"
)

type NetClient struct {
	clients map[string]*rpc.Client
}

func CreateNetClient() *NetClient {
	gob.Register(&RemoteObject{})
	return &NetClient{
		clients: make(map[string]*rpc.Client),
	}
}

func (c *NetClient) Call(hostname string, method string, args interface{}, reply interface{}) {
	var err error
	client := c.clients[hostname]
Retry:
	for client == nil {
		client, err = rpc.Dial("tcp", hostname)
		if err != nil {
			log.Printf("Error connecting to host %s, retrying... [%v]\n", hostname, err)
			client = nil
			time.Sleep(200 * time.Millisecond)
		} else {
			c.clients[hostname] = client
		}
	}
	err = client.Call(method, args, reply)
	if err != nil {
		time.Sleep(time.Second)
		log.Printf("Error calling method \"%s\" on host \"%s\", retrying... [%v]\n", method, hostname, err)
		client.Close()
		delete(c.clients, hostname)
		client = nil
		goto Retry
	}
}

func (c *NetClient) Close() {
	for _, client := range c.clients {
		client.Close()
	}
}
