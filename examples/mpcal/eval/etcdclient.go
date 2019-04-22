package main

import (
	"context"
	"fmt"
	v3 "go.etcd.io/etcd/clientv3"
	"time"
)

type EtcdClient struct {
	client *v3.Client
	ctx    context.Context
	cancel context.CancelFunc
}

func NewEtcdClient(endpoints []string) EtcdClient {
	cfg := v3.Config{
		Endpoints: []string{"http://127.0.0.1:2379"},
	}

	c, err := v3.New(cfg)
	if err != nil {
		panic(err.Error())
	}

	return EtcdClient{client: c}
}

func (c *EtcdClient) Get(key []byte) string {
	value, err := c.getInternal(string(key))
	if err != nil {
		panic(err.Error())
	}
	return value
}

func (c *EtcdClient) getInternal(key string) (string, error) {
	c.ctx, c.cancel = context.WithTimeout(context.Background(), 1000*time.Second)
	response, err := c.client.Get(c.ctx, key)
	if err != nil {
		return "", err
	}
	for _, ev := range response.Kvs {
		if fmt.Sprintf("%s", ev.Key) == key {
			return fmt.Sprintf("%s", ev.Value), nil
		}
	}

	return "", nil
}

func (c *EtcdClient) Put(key []byte, value []byte) {
	c.ctx, c.cancel = context.WithTimeout(context.Background(), 1000*time.Second)
	_, err := c.client.Put(c.ctx, string(key), string(value))
	if err != nil {
		panic(err.Error())
	}
	return
}

func (c *EtcdClient) TearDown() {
	c.client.Close()
	c.cancel()
}

// EXAMPLE USAGE:
/*
	rc := NewEtcdClient([]string{"http://127.0.0.1:2379"})
	defer rc.TearDown()

	var i int
	for (i < 1000) {
		rc.Put([]byte(fmt.Sprintf("key%d", i)), []byte(fmt.Sprintf("val%d", i)))
		res := rc.Get([]byte(fmt.Sprintf("key%d", i)))
		fmt.Println(res)
		i = i+1
	}
*/
