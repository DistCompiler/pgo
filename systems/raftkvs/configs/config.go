package configs

import (
	"errors"
	"time"

	"github.com/spf13/viper"
)

type Root struct {
	NumServers int
	NumClients int

	Debug bool

	Persist bool

	ClientRequestTimeout time.Duration

	FD             FD
	Mailboxes      Mailboxes
	LeaderElection LeaderElection

	AppendEntriesSendInterval time.Duration
	SharedResourceTimeout     time.Duration
	InputChanReadTimeout      time.Duration

	Servers map[int]Server
	Clients map[int]Client
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

type LeaderElection struct {
	Timeout       time.Duration
	TimeoutOffset time.Duration
}

type Server struct {
	MailboxAddr string
	MonitorAddr string
}

type Client struct {
	MailboxAddr string
}

func (r Root) Validate() error {
	if r.NumServers != len(r.Servers) {
		return errors.New("NumServers must be equal to the number of Servers entries")
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
