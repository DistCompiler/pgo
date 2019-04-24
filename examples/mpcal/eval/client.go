package main

type Client interface {
	Get(key string) (string, error)
	Put(key string, value string) error
	Close()
}
