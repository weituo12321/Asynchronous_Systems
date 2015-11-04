---- MODULE MC ----
EXTENDS Lamport, TLC

\* CONSTANT definitions @modelParameterConstants:0Proc
const_144409688206382000 == 
 {1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1NumOfNats
const_144409688207483000 == 
4
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_144409688208584000 ==
0..NumOfNats
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_144409688209685000 ==
Constraint
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_144409688210886000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Oct 05 22:01:22 EDT 2015 by Victor_Hao
