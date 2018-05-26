package distsys

// import (
// 	"time"

// 	. "github.com/onsi/ginkgo"
// 	. "github.com/onsi/gomega"
// )

// var _ = Describe("Server", func() {

// 	var n *NetworkRPC
// 	BeforeEach(func() {
// 		var err error
// 		stateServer, err := NewStateServer(
// 			"127.0.0.1:8080",
// 			"127.0.0.1:8080",
// 			[]string{"127.0.0.1:8080", "127.0.0.1:8081"},
// 			map[string]int{
// 				"a": 0,
// 				"b": 0,
// 				"c": 0,
// 				"e": 1,
// 				"f": 0,
// 			},
// 			map[string]interface{}{
// 				"a": 1,
// 				"b": 2,
// 				"c": 3,
// 				"f": 10,
// 			})
// 		Expect(err).To(BeNil())
// 		// work around the fact that the interface doesn't let us call
// 		// the server functions
// 		n = &NetworkRPC{network: stateServer.(*Network)}
// 	})

// 	AfterEach(func() {
// 		n.network.Close()
// 		time.Sleep(10 * time.Millisecond)
// 	})

// 	var getReply GetRemoteReply
// 	var setReply SetRemoteReply

// 	Context("GetRemote", func() {
// 		It("GetRemote success", func() {
// 			err := n.GetRemote(&GetRemoteArgs{
// 				Host: n.network.localhost,
// 				Transaction: TransactionSet{
// 					Keys: map[string]bool{
// 						"a": true,
// 						"b": true,
// 						"c": true,
// 					},
// 				},
// 			}, &getReply)
// 			Expect(err).To(BeNil())
// 			Expect(getReply.Objects).To(Equal(map[string]RemoteObject{
// 				"a": RemoteObject{Value: 1, Acquired: true},
// 				"b": RemoteObject{Value: 2, Acquired: true},
// 				"c": RemoteObject{Value: 3, Acquired: true},
// 			}))
// 		})

// 		It("GetRemote no-one has it", func() {
// 			err := n.GetRemote(&GetRemoteArgs{
// 				Host: n.network.localhost,
// 				Transaction: TransactionSet{
// 					Keys: map[string]bool{
// 						"a": true,
// 						"d": true,
// 					},
// 				},
// 			}, &getReply)
// 			Expect(err).To(MatchError(
// 				TransactionError(map[string]error{
// 					"d": KeyNotFoundError("d"),
// 				})))
// 		})

// 		It("GetRemote someone else one has it", func() {
// 			err := n.GetRemote(&GetRemoteArgs{
// 				Host: n.network.localhost,
// 				Transaction: TransactionSet{
// 					Keys: map[string]bool{
// 						"a": true,
// 						"e": true,
// 					},
// 				},
// 			}, &getReply)

// 			Expect(err).To(BeNil())
// 			Expect(getReply.Objects).To(Equal(map[string]RemoteObject{
// 				"a": RemoteObject{Value: 1, Acquired: true},
// 			}))
// 			Expect(getReply.Redirects).To(Equal(map[string]string{
// 				"e": "127.0.0.1:8081",
// 			}))
// 		})

// 	})

// 	Context("SetRemote", func() {

// 		BeforeEach(func() {
// 			err := n.GetRemote(&GetRemoteArgs{
// 				Host: n.network.localhost,
// 				Transaction: TransactionSet{
// 					Keys: map[string]bool{
// 						"a": true,
// 						"b": true,
// 						"c": true,
// 						"f": true,
// 					},
// 				},
// 			}, &getReply)
// 			Expect(err).To(BeNil())
// 			Expect(getReply.Objects).To(Equal(map[string]RemoteObject{
// 				"a": RemoteObject{Value: 1, Acquired: true},
// 				"b": RemoteObject{Value: 2, Acquired: true},
// 				"c": RemoteObject{Value: 3, Acquired: true},
// 				"f": RemoteObject{Value: 10, Acquired: true},
// 			}))
// 		})

// 		It("SetRemote success", func() {
// 			err := n.SetRemote(&SetRemoteArgs{
// 				Host: n.network.localhost,
// 				Transaction: TransactionSet{
// 					Keys: map[string]bool{
// 						"a": true,
// 						"b": true,
// 						"c": true,
// 					},
// 				},
// 				Values: map[string]interface{}{
// 					"a": 3,
// 					"b": 2,
// 					"c": 1,
// 				},
// 			},
// 				&setReply)
// 			Expect(err).To(BeNil())
// 			Expect(setReply.Redirects).To(Equal(map[string]string{}))

// 			err = n.GetRemote(&GetRemoteArgs{
// 				Host: n.network.localhost,
// 				Transaction: TransactionSet{
// 					Keys: map[string]bool{
// 						"a": true,
// 						"b": true,
// 						"c": true,
// 					},
// 				},
// 			},
// 				&getReply)
// 			Expect(err).To(BeNil())
// 			Expect(getReply.Objects).To(Equal(map[string]RemoteObject{
// 				"a": RemoteObject{Value: 3, Acquired: true},
// 				"b": RemoteObject{Value: 2, Acquired: true},
// 				"c": RemoteObject{Value: 1, Acquired: true},
// 			}))
// 		})
// 		It("SetRemote no-one has it", func() {
// 			err := n.SetRemote(&SetRemoteArgs{
// 				Host: n.network.localhost,
// 				Transaction: TransactionSet{
// 					Keys: map[string]bool{
// 						"a": true,
// 						"d": true,
// 					},
// 				},
// 				Values: map[string]interface{}{
// 					"a": 3,
// 					"d": 2,
// 				},
// 			},
// 				&setReply)
// 			Expect(err).To(MatchError(
// 				TransactionError(map[string]error{
// 					"d": KeyNotFoundError("d"),
// 				})))
// 		})
// 		It("SetRemote someone else has it", func() {
// 			err := n.SetRemote(&SetRemoteArgs{
// 				Host: n.network.localhost,
// 				Transaction: TransactionSet{
// 					Keys: map[string]bool{
// 						"a": true,
// 						"e": true,
// 						"f": true,
// 					},
// 				},
// 				Values: map[string]interface{}{
// 					"a": 3,
// 					"e": 2,
// 					"f": 6,
// 				},
// 			},
// 				&setReply)
// 			Expect(err).To(BeNil())
// 			Expect(setReply.Redirects).To(Equal(map[string]string{
// 				"e": "127.0.0.1:8081",
// 				"f": "127.0.0.1:8080",
// 			}))

// 			err = n.GetRemote(&GetRemoteArgs{
// 				Host: n.network.localhost,
// 				Transaction: TransactionSet{
// 					Keys: map[string]bool{
// 						"a": true,
// 					},
// 				},
// 			},
// 				&getReply)
// 			Expect(err).To(BeNil())
// 			Expect(getReply.Objects).To(Equal(map[string]RemoteObject{
// 				"a": RemoteObject{Value: 3, Acquired: true},
// 			}))
// 			Expect(getReply.Redirects).To(Equal(map[string]string{}))
// 		})
// 	})

// })
