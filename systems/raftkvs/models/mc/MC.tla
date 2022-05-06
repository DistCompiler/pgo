---- MODULE MC ----
EXTENDS raftkvs, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxNodeFail
const_165164445023143000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2MaxTerm
const_165164445023444000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3ExploreFail
const_165164445023445000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:4LogPop
const_165164445023446000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:5NumClients
const_165164445023447000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6BufferSize
const_165164445023448000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:7NumServers
const_165164445023449000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:8MaxCommitIndex
const_165164445023450000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:9LogConcat
const_165164445023451000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:10Debug
const_165164445023452000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:11LeaderTimeoutReset
const_165164445023453000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:12NumRequests
MCNumRequests ==
1
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_165164445023554000 ==
/\ LimitTerm
/\ LimitCommitIndex
/\ LimitNodeFailure
----
=============================================================================
\* Modification History
\* Created Tue May 03 23:07:30 PDT 2022 by shayan
