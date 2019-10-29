// Agent hunterA in project mushroom_hunters

//{ include("inc/generic_hunter.asl")}
{ include("inc/p2p_dr.asl")}
{ include("common_sense_agent.asl") }

/* Initial beliefs and rules */

agent(hunterA).

rule(l11,hunterA,~edible(M)[source(hunterA)],[destroying_angel(M)[source(any)]]) [rule_type(mapping), context(any)].
rule(l12,hunterA,~edible(M)[source(hunterA)],[death_cap(M)[source(any)]]) [rule_type(mapping), context(any)].
rule(l13,hunterA,edible(M)[source(hunterA)],[caesar_mushroom(M)[source(any)]]) [rule_type(mapping), context(any)].

//focus_rules (simulation)
focus_rule(p11,hunterA, mushroom(m1),[]) [rule_type(defeasible)].
focus_rule(p12,hunterA,has_volva(m1),[]) [rule_type(defeasible)].
focus_rule(p13,hunterA,pale_brownish_cap(m1),[]) [rule_type(defeasible)].
focus_rule(p14,hunterA,patches(m1),[]) [rule_type(defeasible)].
focus_rule(p15,hunterA,cup_margin_lined(m1),[]) [rule_type(defeasible)].
focus_rule(p16,hunterA,~has_annulus(m1),[]) [rule_type(defeasible)].

rule(m11,hunterA, 
	can_collect(M, hunterA)[source(hunterA)], 
	[~max_achieved(hunterA)[source(leader)], edible(M)[source(any)] ]
) [rule_type(mapping), context(any)].

rule(m12,hunterA,edible(M)[source(hunterA)], [edible(M)[source(any)]]) [rule_type(mapping), context(any)]. //considera edible se qualquer outro o considera
rule(m13,hunterA,~edible(M)[source(hunterA)], [~edible(M)[source(any)]]) [rule_type(mapping), context(any)]. //considera não edible se qualquer outro o considera


pref([leader, hunterE, hunterB, hunterC, hunterD]).


/* Initial goals */

!start2.

/* Plans */

+!start2 : true <- .print("hello world from hunter A.");
		!new_query_context(CId);
		!pack_focus_rules(Rf);	
		.my_name(A);
		!query_with_focus_rules(CId, edible(m1), Rf)[source(A)]. // talvez tenha que ser [source(hunterA)]



//+!start2 : true <- .print("hello world from hunter A.");
//		+focus_rules(hunterA, [], [], [], 0);
//		for (focus_rule(N,A,H,B) [rule_type[T]]) {
//			?focus_rules(A, RfH, RfB, RfT, Q)
//			-+focus_rules(A,[H|RfH],[B|RfB],[T|RfT],Q+1);
//		};
//		!new_query_context(CId);
//		?focus_rules(A, RfH, RfB, RfT, Q);
//		!query_with_focus_rules(CId, edible(m1), hunterA, RfH, RfB, RfT, Q).

	