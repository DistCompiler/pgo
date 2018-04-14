package distsys

import (
	"sync"
	"time"

	. "github.com/onsi/ginkgo"
	. "github.com/onsi/gomega"
)

func UnderVariousMigrationPolicies(test func(func() IMigrationPolicy)) {
	Context("No Migration", func() {
		test(func() IMigrationPolicy { return &NeverMigrate{} })
	})
	Context("Always Migration", func() {
		test(func() IMigrationPolicy { return &AlwaysMigrate{} })
	})
	Context("MostFrequentyUsed Migration", func() {
		test(func() IMigrationPolicy {
			return &MostFrequentlyUsed{
				Keys: make(map[string]HostFrequency),
			}
		})
	})
}

var _ = Describe("Client", func() {
	UnderVariousMigrationPolicies(func(makeMigrationPolicy func() IMigrationPolicy) {
		var c1, c2, c3 StateServer

		BeforeEach(func() {
			var err error
			c1, err = MountLocalCache(
				"127.0.0.1:8080",
				"127.0.0.1:8080",
				[]string{"127.0.0.1:8080", "127.0.0.1:8081"},
				map[string]int{
					"a": 0,
					"b": 0,
					"c": 1,
					"d": 1,
				},
				map[string]interface{}{
					"a": 5,
					"b": 6,
				})
			Expect(err).To(BeNil())
			c2, err = MountLocalCache(
				"127.0.0.1:8081",
				"127.0.0.1:8081",
				[]string{"127.0.0.1:8081", "127.0.0.1:8080"},
				map[string]int{
					"a": 1,
					"b": 1,
					"c": 0,
					"d": 0,
				},
				map[string]interface{}{
					"c": 7,
					"d": 8,
				})
			Expect(err).To(BeNil())
			c3, err = MountLocalCache(
				"127.0.0.1:8082",
				"127.0.0.1:8082",
				[]string{"127.0.0.1:8082", "127.0.0.1:8080"},
				map[string]int{
					"a": 0,
					"b": 0,
				},
				map[string]interface{}{},
			)
			Expect(err).To(BeNil())

			c1.SetPolicy(makeMigrationPolicy())
			c2.SetPolicy(makeMigrationPolicy())
			c3.SetPolicy(makeMigrationPolicy())
		})

		AfterEach(func() {
			c1.Close()
			c2.Close()
			c3.Close()
			time.Sleep(10 * time.Millisecond)
		})

		It("Acquire success local", func() {
			_, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{"a", "b"},
				WriteNames: []string{"a", "b"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"a": 5,
				"b": 6,
			}))
		})

		It("Acquire success remote", func() {
			_, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{"c", "d"},
				WriteNames: []string{"c", "d"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 7,
				"d": 8,
			}))
		})
		It("Acquire failure local", func() {
			_, _, err := c3.Acquire(&AcquireSet{
				ReadNames:  []string{"a", "c"},
				WriteNames: []string{"a", "b"},
			})
			Expect(err).To(MatchError(KeyNotFoundError("c")))
		})
		It("Acquire/release read-only local", func() {
			lck, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{"a", "b"},
				WriteNames: []string{},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"a": 5,
				"b": 6,
			}))

			err = c1.Release(lck)
			Expect(err).To(BeNil())
		})
		It("Acquire/release read-only remote", func() {
			lck, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{"c", "d"},
				WriteNames: []string{},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 7,
				"d": 8,
			}))

			err = c1.Release(lck)
			Expect(err).To(BeNil())
		})

		It("Acquire/release write-only local", func() {
			lck, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{},
				WriteNames: []string{"a", "b"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{}))

			err = c1.Release(lck, 1, 2)
			Expect(err).To(BeNil())

			lck, values, err = c1.Acquire(&AcquireSet{
				ReadNames:  []string{"a", "b"},
				WriteNames: []string{},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"a": 1,
				"b": 2,
			}))
		})

		It("Acquire/release read-write local", func() {
			lck, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{"a"},
				WriteNames: []string{"b"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"a": 5,
			}))

			err = c1.Release(lck, 2)
			Expect(err).To(BeNil())

			lck, values, err = c1.Acquire(&AcquireSet{
				ReadNames:  []string{"a", "b"},
				WriteNames: []string{},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"a": 5,
				"b": 2,
			}))
		})

		It("Acquire/release write-only remote", func() {
			lck, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{},
				WriteNames: []string{"c", "d"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{}))

			err = c1.Release(lck, 1, 2)
			Expect(err).To(BeNil())

			lck, values, err = c1.Acquire(&AcquireSet{
				ReadNames:  []string{"c", "d"},
				WriteNames: []string{},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 1,
				"d": 2,
			}))
		})

		It("Acquire/release read-write remote", func() {
			lck, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{"c"},
				WriteNames: []string{"d"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 7,
			}))

			err = c1.Release(lck, 1)
			Expect(err).To(BeNil())

			lck, values, err = c1.Acquire(&AcquireSet{
				ReadNames:  []string{"c", "d"},
				WriteNames: []string{},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 7,
				"d": 1,
			}))
		})

		It("Acquire and release success remote", func() {
			releaseSet, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{"c", "d"},
				WriteNames: []string{"c", "d"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 7,
				"d": 8,
			}))

			err = c1.Release(releaseSet, 100, 101)
			Expect(err).To(BeNil())

			_, values, err = c2.Acquire(&AcquireSet{
				ReadNames:  []string{"c", "d"},
				WriteNames: []string{"c", "d"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 100,
				"d": 101,
			}))
		})

		It("Acquire and release range mismatch", func() {
			releaseSet, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{"c", "d"},
				WriteNames: []string{"c"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 7,
				"d": 8,
			}))

			err = c1.Release(releaseSet, 100, 101)
			Expect(err).To(MatchError(RangeMismatchError{}))
		})

		It("Value changes for single client acquire/release", func() {
			releaseSet, values, err := c1.Acquire(&AcquireSet{
				ReadNames:  []string{"c", "d"},
				WriteNames: []string{"c", "d"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 7,
				"d": 8,
			}))

			err = c1.Release(releaseSet, 100, 101)
			releaseSet, values, err = c1.Acquire(&AcquireSet{
				ReadNames:  []string{"c", "d"},
				WriteNames: []string{"c", "d"},
			})
			Expect(err).To(BeNil())
			Expect(values).To(Equal(map[string]interface{}{
				"c": 100,
				"d": 101,
			}))
		})

		It("Async acquire/release", func(done Done) {
			var wg sync.WaitGroup
			wg.Add(2)

			var acquireLock sync.Mutex
			acquireLock.Lock()

			go func() {
				defer wg.Done()
				defer GinkgoRecover()

				releaseSet, values, err := c1.Acquire(&AcquireSet{
					ReadNames:  []string{"c", "d"},
					WriteNames: []string{"c", "d"},
				})

				Expect(err).To(BeNil())
				Expect(values).To(Equal(map[string]interface{}{
					"c": 7,
					"d": 8,
				}))
				acquireLock.Unlock()

				time.Sleep(50 * time.Millisecond)

				err = c1.Release(releaseSet, 200, 201)
				Expect(err).To(BeNil())
			}()

			go func() {
				defer wg.Done()
				defer GinkgoRecover()

				acquireLock.Lock()

				_, values, err := c2.Acquire(&AcquireSet{
					ReadNames:  []string{"c", "d"},
					WriteNames: []string{"c", "d"},
				})
				Expect(err).To(BeNil())
				Expect(values).To(Equal(map[string]interface{}{
					"c": 200,
					"d": 201,
				}))
			}()

			wg.Wait()
			close(done)
		}, .5)

		It("Acquire and release many times", func() {
			clients := []StateServer{c1, c1, c1, c2, c2, c2, c2, c1, c1}

			for i, c := range clients {
				releaseSet, values, err := c.Acquire(&AcquireSet{
					ReadNames:  []string{"a", "b", "c", "d"},
					WriteNames: []string{"a", "b", "c", "d"},
				})
				Expect(err).To(BeNil())
				Expect(values).To(Equal(map[string]interface{}{
					"a": 5 + 100*i,
					"b": 6 + 100*i,
					"c": 7 + 100*i,
					"d": 8 + 100*i,
				}))

				err = c.Release(releaseSet,
					5+100*(i+1),
					6+100*(i+1),
					7+100*(i+1),
					8+100*(i+1))
				Expect(err).To(BeNil())
			}

		})
	})
})
