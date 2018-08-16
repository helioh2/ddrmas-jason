// Agent hunterA in project mushroom_hunters

//{ include("inc/generic_hunter.asl")}
{ include("inc/p2p_dr.asl")}
{ include("common_sense_agent.asl") }

/* Initial beliefs and rules */

context(hunterA).

mapping_rule(l11,hunterA,~edible(M)[source(hunterA)],[destroying_angel(M)[source(any)]]).
mapping_rule(l12,hunterA,~edible(M)[source(hunterA)],[death_cap(M)[source(any)]]).
mapping_rule(l13,hunterA,edible(M)[source(hunterA)],[caesar_mushroom(M)[source(any)]]).

//perceptions (simulation)
percept(p11,hunterA, mushroom(m1)).
percept(p12,hunterA,has_volva(m1)).
percept(p13,hunterA,pale_brownish_cap(m1)).
percept(p14,hunterA,patches(m1)).
percept(p15,hunterA,cup_margin_lined(m1)).
percept(p16,hunterA,~has_annulus(m1)).

mapping_rule(m11,hunterA, 
	can_collect(M, hunterA)[source(hunterA)], 
	[~max_achieved(hunterA)[source(leader)], edible(M)[source(any)] ]
).

mapping_rule(m12,hunterA,edible(M)[source(hunterA)], [edible(M)[source(any)]]). //considera edible se qualquer outro o considera
mapping_rule(m13,hunterA,~edible(M)[source(hunterA)], [~edible(M)[source(any)]]). //considera edible se qualquer outro o considera

/**
accept_opinions_for(edible(M)).

+accept_opinions_for(X,C) : context(C) <-
	?rule_id(IDN);
	.concat("m",IDN,ID);
	-+rule_id(IDN+1);
	+mapping_rule(ID,C,X[source(C)],[X[source(any)]]);
 */

pref(hunterA, [leader, hunterE, hunterB, hunterC, hunterD]).


/* Initial goals */


!start2.

/* Plans */

+!start2 : true <- .print("hello world from hunter A.");
		+percepts(hunterA,[]);
		for (percept(N,C,P)) {
			?percepts(C,Ps);
			-+percepts(C,[P|Ps]);
		};
		?percepts(C,Ps);
		!p2p_dr_with_percepts(edible(m1),hunterA,hunterA,Ps, edible(m1)).
		

//{ include("$jacamoJar/templates/common-cartago.asl") }
//{ include("$jacamoJar/templates/common-moise.asl") }

// uncomment the include below to have an agent compliant with its organisation
//{ include("$moiseJar/asl/org-obedient.asl") }
