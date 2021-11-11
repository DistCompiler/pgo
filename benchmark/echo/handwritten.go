package echo

import (
	"encoding/gob"
	"log"
	"net"

	"github.com/UBC-NSS/pgo/distsys/tla"
)

type EchoServer struct {
	addr     string
	listener net.Listener
	self     tla.TLAValue
}

func NewEchoServer(addr string, self tla.TLAValue) *EchoServer {
	return &EchoServer{addr: addr, self: self}
}

func (s *EchoServer) ListenAndServe() error {
	var err error
	s.listener, err = net.Listen("tcp", s.addr)
	if err != nil {
		return err
	}

	for {
		conn, err := s.listener.Accept()
		if err != nil {
			return err
		}
		go s.handleConn(conn)
	}
}

func (s *EchoServer) handleConn(conn net.Conn) {
	encoder := gob.NewEncoder(conn)
	decoder := gob.NewDecoder(conn)
	for {
		var req tla.TLAValue
		err := decoder.Decode(&req)
		if err != nil {
			log.Println(err)
			break
		}
		reqBody, ok := req.AsFunction().Get(tla.MakeTLAString("body"))
		if !ok {
			log.Println("body not found in the request")
			break
		}
		resp := tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("from"), Value: s.self},
			{Key: tla.MakeTLAString("body"), Value: reqBody.(tla.TLAValue)},
		})
		err = encoder.Encode(&resp)
		if err != nil {
			log.Println(err)
			break
		}
	}
}

func (s *EchoServer) Close() error {
	return s.listener.Close()
}

type EchoClient struct {
	serverAddr string
	conn       net.Conn
	self       tla.TLAValue

	encoder *gob.Encoder
	decoder *gob.Decoder
}

func NewEchoClient(serverAddr string, self tla.TLAValue) *EchoClient {
	return &EchoClient{
		serverAddr: serverAddr,
		self:       self,
	}
}

func (c *EchoClient) ensureConn() error {
	if c.conn == nil {
		var err error
		c.conn, err = net.Dial("tcp", c.serverAddr)
		if err != nil {
			c.conn, c.encoder, c.decoder = nil, nil, nil
		} else {
			c.encoder = gob.NewEncoder(c.conn)
			c.decoder = gob.NewDecoder(c.conn)
		}
		return err
	}
	return nil
}

func (c *EchoClient) Call(inp tla.TLAValue) (tla.TLAValue, error) {
	err := c.ensureConn()
	if err != nil {
		return tla.TLAValue{}, err
	}

	req := tla.MakeTLARecord([]tla.TLARecordField{
		{Key: tla.MakeTLAString("from"), Value: c.self},
		{Key: tla.MakeTLAString("body"), Value: inp},
	})

	err = c.encoder.Encode(&req)
	if err != nil {
		return tla.TLAValue{}, err
	}
	var resp tla.TLAValue
	err = c.decoder.Decode(&resp)
	respBody := resp.ApplyFunction(tla.MakeTLAString("body"))
	return respBody, err
}

func (c *EchoClient) Close() error {
	return c.conn.Close()
}
