// Agent hunterA in project mushroom_hunters

//{ include("inc/generic_hunter.asl")}
{ include("inc/p2p_dr.asl")}
/* Initial beliefs and rules */

context(hunterD).

mapping_rule(m41,hunterD, ~edible(M)[source(hunterD)], [amanita(M)[source(any)]]).

pref(hunterD, [common_sense_agent, leader, hunterE, hunterB, hunterC, hunterA]).

/* Initial goals */

!start2.

/* Plans */

+!start2 : true <- .print("hello world from hunter D.").

//{ include("$jacamoJar/templates/common-cartago.asl") }
//{ include("$jacamoJar/templates/common-moise.asl") }

// uncomment the include below to have an agent compliant with its organisation
//{ include("$moiseJar/asl/org-obedient.asl") }
