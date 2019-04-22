package main

type Client interface {
	Get(key string) (string, err)
	Put(key string, value string) err
}
