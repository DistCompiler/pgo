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

func (c *PaxosClient) Get(key string) (string, error) {
	var resp map[string]string
	req := map[string]string{
		"key": key,
	}

	leaderAddress := c.addresses[c.leaderId]
	if err := c.connections[leaderAddress].Call("KVService.Get", req, &resp); err != nil {
		return "", err
	}

	// TODO: check if leader (resp["type"])
	return resp["result"], nil
}

func (c *PaxosClient) Put(key string, value string) error {
	var resp map[string]string
	req := map[string]string{
		"key":   key,
		"value": value,
	}

	leaderAddress := c.addresses[c.leaderId]
	if err := c.connections[leaderAddress].Call("KVService.Put", req, &resp); err != nil {
		return err
	}

	// TODO: check if leader (resp["type"])
	return nil
}

func (c *PaxosClient) Close() {
	// no-op
}
