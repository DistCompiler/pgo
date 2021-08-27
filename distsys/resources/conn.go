package resources

import (
	"io"
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
	if deadlineErr := rw.conn.SetReadDeadline(time.Time{}); deadlineErr != nil {
		return n, deadlineErr
	}
	return
}

func (rw readWriterConnTimeout) Write(data []byte) (n int, err error) {
	if deadlineErr := rw.conn.SetWriteDeadline(time.Now().Add(rw.timeout)); deadlineErr != nil {
		return 0, deadlineErr
	}
	n, err = rw.conn.Write(data)
	if deadlineErr := rw.conn.SetWriteDeadline(time.Time{}); deadlineErr != nil {
		return n, deadlineErr
	}
	return
}
