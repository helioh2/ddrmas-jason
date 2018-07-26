// Agent peerC3 in project mushroom_hunters

{ include("inc/p2p_dr.asl") }

/* Initial beliefs and rules */

context(peerC3).

strict_rule(l31,peerC3,lit(a3)[source(peerC3)],[]).

pref(peerC3, [peerC1,
			peerC2,
			peerC4,
			peerC5,
			peerC6]).

/* Initial goals */

!start.

/* Plans */

+!start : true <- .print("hello world.").

{ include("$jacamoJar/templates/common-cartago.asl") }
{ include("$jacamoJar/templates/common-moise.asl") }

// uncomment the include below to have an agent compliant with its organisation
//{ include("$moiseJar/asl/org-obedient.asl") }
