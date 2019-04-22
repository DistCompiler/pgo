package main

import (
	"fmt"
	"time"
	"context"
	v3 "go.etcd.io/etcd/clientv3"
)

type RaftClient struct {
	client *v3.Client
	ctx context.Context
	cancel context.CancelFunc
}

func getVal(client *v3.Client, ctx context.Context, key string) (string, error) {
	gresp, err := client.Get(ctx, key)
	if err != nil {
		return "", err
	}
	for _, ev := range gresp.Kvs {
		if (fmt.Sprintf("%s", ev.Key) == key) {
			return fmt.Sprintf("%s", ev.Value), nil
		}
	}

	return "", nil
}

func newRaftClient(endpoints []string) RaftClient {
	cfg := v3.Config{
		Endpoints: []string{"http://127.0.0.1:2379"},
	}

	c, err := v3.New(cfg)
	if err != nil {
		panic(err.Error())
	}

	ctx, cancel := context.WithTimeout(context.Background(), 1000*time.Second)
	return RaftClient{c,ctx,cancel}
}

func (c RaftClient) issueGet(key []byte) (string) {
	res,err := getVal(c.client, c.ctx, string(key))
	if err != nil {
		panic(err.Error())
	}
	return res
}

func (c RaftClient) issuePut(key []byte, value []byte) {
	_,err := c.client.Put(c.ctx, string(key), string(value))
	if err != nil {
		panic(err.Error())
	}
	return
}

func (c RaftClient) tearDown() {
	c.client.Close()
	c.cancel()
}

// EXAMPLE USAGE:
/*
	rc := newRaftClient([]string{"http://127.0.0.1:2379"})
	defer rc.tearDown()

	var i int
	for (i < 1000) {
		rc.issuePut([]byte(fmt.Sprintf("key%d", i)), []byte(fmt.Sprintf("val%d", i)))
		res := rc.issueGet([]byte(fmt.Sprintf("key%d", i)))
		fmt.Println(res)
		i = i+1
	}
/*
