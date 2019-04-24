package main

import (
	"fmt"
)

type DummyClient struct{}

func NewDummyClient() *DummyClient {
	return &DummyClient{}
}

func (c *DummyClient) Get(key string) (string, error) {
	fmt.Printf("getting %s\n", key)
	return "value", nil
}

func (c *DummyClient) Put(key, value string) error {
	fmt.Printf("putting %s %s\n", key, value)
	return nil
}

func (c *DummyClient) Close() {
}
