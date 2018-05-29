package distsys

import (
	. "github.com/onsi/ginkgo"
	. "github.com/onsi/gomega"

	"testing"
)

var _ = Describe("Distsys package", func() {
	var (
		ownershipTable *OwnershipTable
		stateHandler   localStateHandler
		store          *SimpleDataStore
		group          *VarReq
		self           = "10.10.10.2"
	)

	BeforeEach(func() {
		ownershipTable = NewOwnershipTable(map[string]string{
			"a": "10.10.10.10",
			"b": "10.10.10.20",
			"c": "10.10.10.30",
		}, self)
	})

	var _ = Describe("localStateHandler", func() {
		BeforeEach(func() {
			// current state of the underlying global state store in the running node
			store = NewSimpleDataStore(map[string]interface{}{
				"a": 10,
				"b": 20,
				"c": 30,
			})

			// which group of variables is being requested
			group = &VarReq{
				Peer: self,
				Names: []*BorrowSpecVariable{
					&BorrowSpecVariable{Name: "a", Exclusive: true},
					&BorrowSpecVariable{Name: "c", Exclusive: false},
				},
			}

			stateHandler = localStateHandler{
				group:             group,
				store:             store,
				ownership:         ownershipTable,
				migrationStrategy: NeverMigrate(self),
			}
		})

		var _ = Describe("GetState", func() {
			It("returns a series of values when all of the state is owned by that peer", func() {
				ownershipTable.table["a"].address = self
				ownershipTable.table["b"].address = self
				ownershipTable.table["c"].address = self

				refs, _ := stateHandler.GetState()
				Expect(len(refs)).To(Equal(2))

				Expect(refs["a"]).To(Equal(&Reference{
					Type: REF_VAL,

					Value:     10,
					Exclusive: true,
					Ownership: false,
				}))
				Expect(refs["c"]).To(Equal(&Reference{
					Type: REF_VAL,

					Value:     30,
					Exclusive: false,
					Ownership: false,
				}))
			})

			It("returns a moved value when the running node no longer owns a variable", func() {
				// current node owns variable 'a', but not 'c'
				ownershipTable.table["a"].address = self

				refs, _ := stateHandler.GetState()
				Expect(len(refs)).To(Equal(2))

				Expect(refs["a"]).To(Equal(&Reference{
					Type:      REF_VAL,
					Value:     10,
					Exclusive: true,
					Ownership: false,
				}))
				Expect(refs["c"]).To(Equal(&Reference{
					Type: REF_MOVED,
					Peer: "10.10.10.30",
				}))
			})

			It("skips values that it owns if previous variables moved", func() {
				// request for variables 'a', 'b' and 'c'
				group.Names = append(group.Names, group.Names[1])
				group.Names[1] = &BorrowSpecVariable{Name: "b", Exclusive: true}

				// running node owns 'a' and 'c', but not 'b'
				ownershipTable.table["a"].address = self
				ownershipTable.table["c"].address = self

				refs, _ := stateHandler.GetState()
				Expect(len(refs)).To(Equal(3))

				Expect(refs["a"]).To(Equal(&Reference{
					Type:      REF_VAL,
					Value:     10,
					Exclusive: true,
					Ownership: false,
				}))

				Expect(refs["b"]).To(Equal(&Reference{
					Type: REF_MOVED,
					Peer: "10.10.10.20",
				}))

				Expect(refs["c"]).To(Equal(&Reference{
					Type: REF_SKIP,
				}))
			})

			It("indicates all variables that have moved", func() {
				// request for variables 'a', 'b' and 'c'
				group.Names = append(group.Names, group.Names[1])
				group.Names[1] = &BorrowSpecVariable{Name: "b", Exclusive: true}

				// running node owns 'a', but not 'b' and 'c'
				ownershipTable.table["a"].address = self

				refs, _ := stateHandler.GetState()
				Expect(len(refs)).To(Equal(3))

				Expect(refs["a"]).To(Equal(&Reference{
					Type:      REF_VAL,
					Value:     10,
					Exclusive: true,
					Ownership: false,
				}))

				Expect(refs["b"]).To(Equal(&Reference{
					Type: REF_MOVED,
					Peer: "10.10.10.20",
				}))

				Expect(refs["c"]).To(Equal(&Reference{
					Type: REF_MOVED,
					Peer: "10.10.10.30",
				}))
			})
		})
	})
})

func TestStateOwnership(t *testing.T) {
	RegisterFailHandler(Fail)
	RunSpecs(t, "StateOwnership")
}
