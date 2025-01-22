val aClientDefns = List(
  "AClient.reqCh=mapping:client_reqCh",
  "AClient.net=mapping:network",
  "AClient.req=local:req",
  "AClient.reqIdx=local:reqIdx",
  "AClient.leader=local:leader0",
  "AClient.resp=local:resp",
  "AClient.respCh=mapping:client_respCh"
)

def withPrefix(prefix: String)(assigns: String*): Seq[String] =
  assigns.map(assign => s"$prefix.$assign")

val aServerDefns = withPrefix("AServer")(
  "idx=local:idx",
  "m=local:m",
  "srvId=local:srvId",
  "net=mapping:network",
  "netLen=mapping:networkLen",
  "state=global:state",
  "currentTerm=global:currentTerm",
  "votedFor=global:votedFor",
  "votesResponded=global:votesResponded",
  "votesGranted=global:votesGranted",
  "leader=global:leader",
  "leaderTimeout=global:leaderTimeout",
  "commitIndex=global:commitIndex",
  "nextIndex=global:nextIndex",
  "matchIndex=global:matchIndex",
  "log=global:log",
  "plog=mapping:persistentLog",
  "sm=global:sm",
  "smDomain=global:smDomain",
  "becomeLeaderCh=mapping:becomeLeaderCh",
  "appendEntriesCh=mapping:appendEntriesCh",
  "fd=mapping:fd"
)

val aServerRequestVoteDefns = withPrefix("AServerRequestVote")(
  "idx=local:idx0",
  "srvId=local:srvId0",
  "net=mapping:network",
  "netLen=mapping:networkLen",
  "state=global:state",
  "currentTerm=global:currentTerm",
  "votedFor=global:votedFor",
  "votesResponded=global:votesResponded",
  "votesGranted=global:votesGranted",
  "leader=global:leader",
  "leaderTimeout=global:leaderTimeout",
  "log=global:log",
  "fd=mapping:fd"
)

val aServerAppendEntriesDefns = withPrefix("AServerAppendEntries")(
  "idx=local:idx1",
  "srvId=local:srvId1",
  "net=mapping:network",
  "netLen=mapping:networkLen",
  "state=global:state",
  "currentTerm=global:currentTerm",
  "votedFor=global:votedFor",
  "votesResponded=global:votesResponded",
  "votesGranted=global:votesGranted",
  "commitIndex=global:commitIndex",
  "nextIndex=global:nextIndex",
  "matchIndex=global:matchIndex",
  "leader=global:leader",
  "leaderTimeout=global:leaderTimeout",
  "appendEntriesCh=mapping:appendEntriesCh",
  "log=global:log",
  "fd=mapping:fd"
)

val aServerAdvanceCommitIndex = withPrefix("AServerAdvanceCommitIndex")(
  "newCommitIndex=local:newCommitIndex",
  "srvId=local:srvId2",
  "net=mapping:network",
  "netLen=mapping:networkLen",
  "state=global:state",
  "currentTerm=global:currentTerm",
  "votedFor=global:votedFor",
  "votesResponded=global:votesResponded",
  "votesGranted=global:votesGranted",
  "leader=global:leader",
  "commitIndex=global:commitIndex",
  "nextIndex=global:nextIndex",
  "matchIndex=global:matchIndex",
  "sm=global:sm",
  "smDomain=global:smDomain",
  "leaderTimeout=global:leaderTimeout",
  "log=global:log",
  "plog=mapping:persistentLog"
)

val aServerBecomeLeader = withPrefix("AServerBecomeLeader")(
  "srvId=local:srvId3",
  "becomeLeaderCh=mapping:becomeLeaderCh",
  "state=global:state",
  "votedFor=global:votedFor",
  "votesResponded=global:votesResponded",
  "votesGranted=global:votesGranted",
  "log=global:log",
  "plog=mapping:persistentLog",
  "commitIndex=global:commitIndex",
  "nextIndex=global:nextIndex",
  "matchIndex=global:matchIndex",
  "leader=global:leader",
  "currentTerm=global:currentTerm",
  "appendEntriesCh=mapping:appendEntriesCh",
  "becomeLeaderCh=mapping:becomeLeaderCh"
)

val aServerCrasher = withPrefix("AServerCrasher")(
  "srvId=local:srvId4"
)

os.proc(
  "scala-cli",
  "run",
  ".",
  "--main-class",
  "pgo.PGo",
  "--",
  "pcalgen",
  "--spec-file",
  os.pwd / "tmp2" / "raftkvs.tla"
).call(
  cwd = os.pwd,
  mergeErrIntoOut = true,
  stdout = os.Inherit
)

val proc =
  os.proc(
    "scala-cli",
    "run",
    ".",
    "--main-class",
    "pgo.PGo",
    "--",
    "tracegen",
    "-d",
    "tmp2/",
    "--model-name",
    "raftkvs",
    "--trace-files",
    os.list(os.pwd / "systems" / "raftkvs").filter(_.ext == "log"),
    "--mpcal-variable-defns",
    aClientDefns,
    aServerDefns,
    aServerRequestVoteDefns,
    aServerAppendEntriesDefns,
    aServerAdvanceCommitIndex,
    aServerBecomeLeader,
    aServerCrasher,
    "--mpcal-state-vars",
    "plog",
    "becomeLeaderCh",
    "respCh",
    "requestVoteSrvId",
    "appendEntriesSrvId",
    "advanceCommitIndexSrvId",
    "becomeLeaderSrvId",
    "crasherSrvId",
    "timeout",
    "fd",
    "network",
    "reqCh",
    "appendEntriesCh",
    "--mpcal-constant-defns",
    "Debug=FALSE",
    "ExploreFail=FALSE",
    "BufferSize=100",
    "MaxTerm=999999",
    "MaxCommitIndex=999999",
    "MaxNodeFail=99",
    "LeaderTimeoutReset=100",
    "NumServers=3",
    "NumClients=1",
    "NumRequests=3", // sus: allReqs has a length of 3
    "AllStrings=__all_strings",
    "--model-values",
    "LogConcat",
    "LogPop"
  )

println(proc.commandChunks.mkString(" "))

val result = proc.call(cwd = os.pwd, check = false, mergeErrIntoOut = true)

if result.exitCode == 0
then println("generated ok")
else result.out.lines().foreach(println)
