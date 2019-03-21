// Agent hunterA in project mushroom_hunters

//{ include("inc/generic_hunter.asl")}
{ include("inc/p2p_dr.asl")}
{ include("common_sense_agent.asl") }

/* Initial beliefs and rules */

context(hunterA).

mapping_rule(l11,hunterA,~edible(M)[source(hunterA)],[destroying_angel(M)[source(any)]]).
mapping_rule(l12,hunterA,~edible(M)[source(hunterA)],[death_cap(M)[source(any)]]).
mapping_rule(l13,hunterA,edible(M)[source(hunterA)],[caesar_mushroom(M)[source(any)]]).

//focus_rules (simulation)
focus_rule(p11,hunterA, mushroom(m1)).
focus_rule(p12,hunterA,has_volva(m1)).
focus_rule(p13,hunterA,pale_brownish_cap(m1)).
focus_rule(p14,hunterA,patches(m1)).
focus_rule(p15,hunterA,cup_margin_lined(m1)).
focus_rule(p16,hunterA,~has_annulus(m1)).

mapping_rule(m11,hunterA, 
	can_collect(M, hunterA)[source(hunterA)], 
	[~max_achieved(hunterA)[source(leader)], edible(M)[source(any)] ]
).

mapping_rule(m12,hunterA,edible(M)[source(hunterA)], [edible(M)[source(any)]]). //considera edible se qualquer outro o considera
mapping_rule(m13,hunterA,~edible(M)[source(hunterA)], [~edible(M)[source(any)]]). //considera não edible se qualquer outro o considera


pref(hunterA, [leader, hunterE, hunterB, hunterC, hunterD]).


/* Initial goals */

!start2.

/* Plans */

+!start2 : true <- .print("hello world from hunter A.");
		+focus_rules(hunterA,[]);
		for (focus_rule(N,C,P)) {
			?focus_rules(C,Ps);
			-+focus_rules(C,[P|Ps]);
		};
		?focus_rules(C,Ps);
		!p2p_dr_with_focus_rules(edible(m1),hunterA,hunterA,Ps, edible(m1)).

	