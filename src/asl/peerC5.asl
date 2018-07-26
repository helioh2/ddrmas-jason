// Agent peerC5 in project mushroom_hunters
{ include("inc/p2p_dr.asl") }
/* Initial beliefs and rules */

context(peerC5).

strict_rule(l51,peerC5,lit(a5)[source(peerC5)],[]).

pref(peerC5, [peerC3,
			peerC2,
			peerC4,
			peerC1,
			peerC6]).

/* Initial goals */

!start.

/* Plans */

+!start : true <- .print("hello world.").

{ include("$jacamoJar/templates/common-cartago.asl") }
{ include("$jacamoJar/templates/common-moise.asl") }

// uncomment the include below to have an agent compliant with its organisation
//{ include("$moiseJar/asl/org-obedient.asl") }
