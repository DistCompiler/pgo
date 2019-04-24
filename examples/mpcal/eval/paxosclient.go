package main

import (
	"net/rpc"
)

type PaxosClient struct {
	connections map[string]*rpc.Client // RPC connections to Paxos KV servers
	addresses   []string               // list of available servers
	leaderId    int                    // index into addresses of the node believed to be the leader
}

func NewPaxosClient(addresses []string) (*PaxosClient, error) {
	connections := make(map[string]*rpc.Client, len(addresses))

	for _, addr := range addresses {
		rpcClient, err := rpc.Dial("tcp", addr)
		if err != nil {
			return nil, err
		}

		connections[addr] = rpcClient
	}

	return &PaxosClient{
		connections: connections,
		addresses:   addresses,
	}, nil
}

func (c *PaxosClient) requestLoop(service string, request map[string]string) (map[string]string, error) {
	var resp map[string]string

	for {
		leaderAddress := c.addresses[c.leaderId]
		if err := c.connections[leaderAddress].Call("KVService.Get", request, &resp); err != nil {
			return nil, err
		}

		if resp["type"] == "not_leader_msg" {
			c.leaderId = (c.leaderId + 1) % len(c.addresses) // start from scratch if needed
			continue                                         // try again
		}

		return resp, nil
	}
}

func (c *PaxosClient) Get(key string) (string, error) {
	req := map[string]string{
		"key": key,
	}

	var resp map[string]string
	var err error

	resp, err = c.requestLoop("KVService.Get", req)
	if err != nil {
		return "", err
	}

	return resp["result"], nil
}

func (c *PaxosClient) Put(key string, value string) error {
	req := map[string]string{
		"key":   key,
		"value": value,
	}

	_, err := c.requestLoop("KVService.Put", req)
	return err
}

func (c *PaxosClient) Close() {
	// no-op
}
