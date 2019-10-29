// Agent hunterA in project mushroom_hunters

//{ include("inc/generic_hunter.asl")}
{ include("inc/p2p_dr.asl")}
{ include("common_sense_agent.asl") }

/* Initial beliefs and rules */

agent(hunterB).
rule(m21,hunterB, ~edible(M)[source(hunterB)], [has_volva(M)[source(hunterB)]]) [rule_type(mapping), context(any)].

pref(hunterB, [hunterE, hunterA, hunterC, hunterD]).


/* Initial goals */

!start2.

/* Plans */

+!start2 : true <- .print("hello world from hunter B.").
