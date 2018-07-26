// Agent peerC5 in project mushroom_hunters
{ include("inc/p2p_dr.asl") }
/* Initial beliefs and rules */

context(peerC6).

defeasible_rule(d61,peerC6,lit(a6)[source(peerC6)],[]).
strict_rule(l61,peerC6,~lit(a6)[source(peerC6)],[]).

pref(peerC6, [peerC3,
			peerC2,
			peerC4,
			peerC5,
			peerC1]).

/* Initial goals */

!start.

/* Plans */

+!start : true <- .print("hello world.").

{ include("$jacamoJar/templates/common-cartago.asl") }
{ include("$jacamoJar/templates/common-moise.asl") }

// uncomment the include below to have an agent compliant with its organisation
//{ include("$moiseJar/asl/org-obedient.asl") }
