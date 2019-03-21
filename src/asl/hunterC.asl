// Agent hunterA in project mushroom_hunters

//{ include("inc/generic_hunter.asl")}
{ include("inc/p2p_dr.asl")}
{ include("common_sense_agent.asl") }
/* Initial beliefs and rules */

context(hunterC).

mapping_rule(m31,hunterC, edible(M)[source(hunterC)], [springtime_amanita(M)[source(any)]]).

pref(hunterC, [leader, hunterE, hunterB, hunterA, hunterD]).


/* Initial goals */

!start2.

/* Plans */

+!start2 : true <- .print("hello world from hunter C.").
