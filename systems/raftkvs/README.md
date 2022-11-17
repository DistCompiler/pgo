# raftkvs

raftkvs is a key-value store based on the Raft consensus protocol.

## Model

raftkvs has two set of nodes: server and client.

A server has several archetypes that run concurrently. `AServerHandler` handles
the incoming messages in a server. `AServerRequestVote` starts a new election
round in case of a leader timeout. `AServerBecomeLeader` detects if the current
server has a quorum of votes and then promotes itself to be the leader. If the
current server is the leader, `AServerAppendEntries` broadcasts new entries, and
`AServerAdvanceCommitIndex` increases the commit index.

A client has an archetype `AClient` that receives input requests from a channel
(`reqCh`) and sends them to a server. Then it receives the response and returns
it to the user via another channel (`respCh`).

### Assumptions

The makes the following assumption for the environment during model checking:

1. Network links are reliable FIFO links, which is modeled by `ReliableFIFOLink` mapping macro.
2. The failure detector used is a theoretically perfect failure detector.
3. Servers might fail with respect to the crash-stop failure semantics. Crashed servers cannot
rejoin the system.
4. Reconfiguration is not supported, therefore, the set of servers is static.

### Properties

The following five properties are the properties defined by the original Raft
paper.

- `ElectionSafety`: at most one leader can be elected in a given term. 
- `LogMatching`: if two logs contain an entry with the same index and term, then
  the logs are identical in all entries up through the given index.
- `LeaderCompleteness`: if a log entry is committed in a given term, then that
  entry will be present in the logs of the leaders for all higher-numbered
  terms.
- `StateMachineSafety`: if a server has applied a log entry at a given index to
  its state machine, no other server will ever apply a different log entry for
  the same index.
- `LeaderAppendOnly`: a leader never overwrites or deletes entries in its log;
  it only appends new entries.

Moreover, we have defined some extra properties as well:

- `ApplyLogOK`: committed log entries are correctly reflected in the key-value store dictionary.
- `plogOK`: persistent log is update correctly.
- `ClientsOK`: clients will eventually receive a response for the corresponding
  request. This property will be violated if servers can crash, i.e.,
  `ExploreFail` set to be true.
- `ElectionLiveness`: eventually a server will be elected as the leader. This
  will be violated if the number of servers are more than one.

### Constraints

`LimitTerm` and `LimitCommitIndex` limit servers term and commit index respectively.
`LimitNodeFailure` limits the number of crashing nodes.

## Usage

### Verification

Configurations can be found in the [`models`](/systems/raftkvs/models/) folder.

```sh
make mc  # TLC model checking
make sim # TLC simulation, useful for fiding 
```

### Build

```sh
make build
```

### Run

Sample config files can be found in the [`configs`](/systems/raftkvs/configs/) folder.

```sh
./server -srvId <server_id> -c <path/to/config.yaml>
./client -clientId <client_id> -c <path/to/config.yaml>
```

### Test

```
make test
make racetest
```

### Benchmark

Our fork of [Go YCSB](https://github.com/shayanh/go-ycsb) supports raftkvs. For
more details, check it out.