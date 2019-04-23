package main

import (
    "github.com/ha/doozer"
)

type DoozerClient struct {
    conn *doozer.Conn
    oldRev int64
}

func DialDoozer(uri string, buri string) (*DoozerClient, error) {
    conn, err := doozer.DialUri(uri, buri)
    if err != nil {
        return nil, err
    }
    return &DoozerClient{conn, 0}, nil
}

func(c *DoozerClient) Close() {
    c.conn.Close()
}

func(c *DoozerClient) Get(key string) (string, error) {
    value, rev, err := c.conn.Get("/"+key, nil)
    if err != nil {
        return "", err
    }
    c.oldRev = rev
    return string(value), nil
}

func(c *DoozerClient) Put(key string, value string) error {
    for {
        newRev, err := c.conn.Set("/"+key, c.oldRev, []byte(value))
        if err == doozer.ErrOldRev {
            newRev, err = c.conn.Rev()
            if err != nil {
                return err
            }
            c.oldRev = newRev
        } else {
            if err != nil {
                return err
            }
            c.oldRev = newRev
            return nil
        }
    }
}

