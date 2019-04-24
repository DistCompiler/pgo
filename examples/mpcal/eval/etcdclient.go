package main

import (
	"context"
	v3 "go.etcd.io/etcd/clientv3"
	"time"
)

type EtcdClient struct {
	client *v3.Client
	kv     v3.KV
	ctx    context.Context
	cancel context.CancelFunc
}

func NewEtcdClient(endpoint string) (*EtcdClient, error) {
	cfg := v3.Config{
		Endpoints: []string{endpoint},
	}

	c, err := v3.New(cfg)
	if err != nil {
		return nil, err
	}

	return &EtcdClient{client: c, kv: v3.NewKV(c)}, nil
}

func (c *EtcdClient) Get(key string) (string, error) {
	c.ctx, c.cancel = context.WithTimeout(context.Background(), 1000*time.Second)
	response, err := c.kv.Get(c.ctx, key)
	if err != nil {
		return "", err
	}
	for _, ev := range response.Kvs {
		if string(ev.Key) == key {
			return string(ev.Value), nil
		}
	}

	return "", nil
}

func (c *EtcdClient) Put(key string, value string) error {
	c.ctx, c.cancel = context.WithTimeout(context.Background(), 1000*time.Second)
	_, err := c.kv.Put(c.ctx, key, value)
	return err
}

func (c *EtcdClient) Close() {
	c.cancel()
	c.client.Close()
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
