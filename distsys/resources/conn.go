package resources

import (
	"io"
	"log"
	"net"
	"time"
)

type readWriterConnTimeout struct {
	conn    net.Conn
	timeout time.Duration
}

var _ io.ReadWriter = &readWriterConnTimeout{}

func makeReadWriterConnTimeout(conn net.Conn, timeout time.Duration) readWriterConnTimeout {
	return readWriterConnTimeout{
		conn:    conn,
		timeout: timeout,
	}
}

func (rw readWriterConnTimeout) Read(data []byte) (n int, err error) {
	if deadlineErr := rw.conn.SetReadDeadline(time.Now().Add(rw.timeout)); deadlineErr != nil {
		return 0, deadlineErr
	}
	n, err = rw.conn.Read(data)
	if err != nil {
		log.Println("conn read err", err)
	}
	if deadlineErr := rw.conn.SetReadDeadline(time.Time{}); deadlineErr != nil {
		return 0, deadlineErr
	}
	return
}

func (rw readWriterConnTimeout) Write(data []byte) (n int, err error) {
	if deadlineErr := rw.conn.SetWriteDeadline(time.Now().Add(rw.timeout)); deadlineErr != nil {
		return 0, deadlineErr
	}
	n, err = rw.conn.Write(data)
	if err != nil {
		log.Println("conn write err", err)
	}
	if deadlineErr := rw.conn.SetWriteDeadline(time.Time{}); deadlineErr != nil {
		return 0, deadlineErr
	}
	return
}

// type readWriteCloserConnTimeout struct {
// 	readWriterConnTimeout
// 	io.Closer
// }

// func makeReadWriteCloserConnTimeout(conn net.Conn, timeout time.Duration) readWriteCloserConnTimeout {
// 	return readWriteCloserConnTimeout{
// 		readWriterConnTimeout: makeReadWriterConnTimeout(conn, timeout),
// 		Closer:                conn,
// 	}
// }
