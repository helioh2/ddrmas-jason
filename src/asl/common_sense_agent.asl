// Agent hunterA in project mushroom_hunters

{ include("inc/p2p_dr.asl")}

/* Initial beliefs and rules */


context(common_sense_agent).

strict_rule(lcs1, common_sense_agent, amanita(M), [springtime_amanita(M)]).

pref(common_sense_agent, [hunterA, leader, hunterE, hunterB, hunterC, hunterD]).

/* Initial goals */

!start.

/* Plans */

+!start : true <- .print("hello world.").

{ include("$jacamoJar/templates/common-cartago.asl") }
//{ include("$jacamoJar/templates/common-moise.asl") }

// uncomment the include below to have an agent compliant with its organisation
//{ include("$moiseJar/asl/org-obedient.asl") }
