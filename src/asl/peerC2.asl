// Agent peerC2 in project mushroom_hunters

{ include("inc/p2p_dr.asl") }

/* Initial beliefs and rules */

context(peerC2).

mapping_rule(m21,peerC2,lit(a2)[source(peerC2)], [lit(a5)[source(peerC5)]]).
mapping_rule(m22,peerC2,~lit(a2)[source(peerC2)], [lit(a6)[source(peerC6)]]).

pref(peerC2, [peerC3,
			peerC1,
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
