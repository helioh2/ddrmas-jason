
{ include("inc/p2p_dr.asl")}
{ include("common_sense_agent.asl") }
/* Initial beliefs and rules */

context(hunterD).

mapping_rule(m41, hunterD, ~edible(M)[source(hunterD)], [amanita(M)[source(any)]]).

pref(hunterD, [leader, hunterE, hunterB, hunterC, hunterA]).

/* Initial goals */

!start2.

/* Plans */

+!start2 : true <- .print("hello world from hunter D.").

