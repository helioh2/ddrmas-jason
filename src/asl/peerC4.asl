// Agent peerC4 in project mushroom_hunters
{ include("inc/p2p_dr.asl") }
/* Initial beliefs and rules */

context(peerC4).

strict_rule(l41,peerC4,lit(a4)[source(peerC4)],[]).

pref(peerC4, [peerC3,
			peerC2,
			peerC1,
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
