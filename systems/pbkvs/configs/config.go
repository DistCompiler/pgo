package configs

import (
	"errors"
	"time"

	"github.com/spf13/viper"
)

type Root struct {
	NumReplicas int
	NumClients  int

	Debug bool

	ClientRequestTimeout time.Duration

	FD        FD
	Mailboxes Mailboxes

	InputChanReadTimeout time.Duration

	Replicas map[int]Replica
	Clients  map[int]Client
}

type FD struct {
	PullInterval time.Duration
	Timeout      time.Duration
}

type Mailboxes struct {
	ReceiveChanSize int
	DialTimeout     time.Duration
	ReadTimeout     time.Duration
	WriteTimeout    time.Duration
}

type Replica struct {
	ReqMailboxAddr  string
	RespMailboxAddr string
	MonitorAddr     string
}

type Client struct {
	ReqMailboxAddr  string
	RespMailboxAddr string
}

func (r Root) Validate() error {
	if r.NumReplicas != len(r.Replicas) {
		return errors.New("NumReplicas must be equal to the number of Replicas entries")
	}
	if r.NumClients != len(r.Clients) {
		return errors.New("NumClients must be equal to the number of Clients entries")
	}
	return nil
}

func ReadConfig(path string) (Root, error) {
	viper.SetConfigFile(path)
	if err := viper.ReadInConfig(); err != nil {
		return Root{}, err
	}
	var c Root
	err := viper.Unmarshal(&c)
	if err != nil {
		return c, err
	}
	return c, c.Validate()
}
