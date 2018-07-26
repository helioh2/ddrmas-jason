// Agent peerC1 in project mushroom_hunters

{ include("inc/p2p_dr.asl") }

/* Initial beliefs and rules */

context(peerC1).

strict_rule(l11,peerC1,lit(x1)[source(peerC1)], [lit(a1)[source(peerC1)]]).
strict_rule(l12,peerC1,lit(y1)[source(peerC1)],[]).
strict_rule(l12,peerC1,lit(y2)[source(peerC1)],[lit(y1)[source(peerC1)]]).
strict_rule(l12,peerC1,lit(y3)[source(peerC1)],[lit(y2)[source(peerC1)]]).


mapping_rule(m11,peerC1,lit(a1)[source(peerC1)], [lit(a2)[source(peerC2)]]).
mapping_rule(m12,peerC1,~lit(a1)[source(peerC1)], [lit(a3)[source(peerC3)], lit(a4)[source(peerC4)]]).

pref(peerC1, [peerC3,
			peerC2,
			peerC4,
			peerC5,
			peerC6]).

/* Initial goals */

!start.
!p2p_dr_front(lit(x1),peerC1).

/* Plans */

+!start : true <- .print("hello world.").

//{ include("$jacamoJar/templates/common-cartago.asl") }
//{ include("$jacamoJar/templates/common-moise.asl") }

// uncomment the include below to have an agent compliant with its organisation
//{ include("$moiseJar/asl/org-obedient.asl") }
