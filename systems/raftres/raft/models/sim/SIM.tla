---- MODULE SIM ----
EXTENDS raft, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxNodeFail
const_16516444010382000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:2MaxTerm
const_16516444010403000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3ExploreFail
const_16516444010414000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:4LogPop
const_16516444010415000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6BufferSize
const_16516444010417000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:7NumServers
const_16516444010418000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:8MaxCommitIndex
const_16516444010419000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:9LogConcat
const_165164440104110000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:10Debug
const_165164440104111000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11LeaderTimeoutReset
const_165164440104112000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:12NumRequests
SIMNumRequests ==
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_165164440104113000 ==
LimitNodeFailure
----
=============================================================================
\* Modification History
\* Created Tue May 03 23:06:41 PDT 2022 by shayan
