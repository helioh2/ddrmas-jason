{ include("inc/p2p_dr.asl")}
{ include("common_sense_agent.asl") }
/* Initial beliefs and rules */

agent(hunterE).

rule(l51, hunterE, springtime_amanita(M)[source(hunterE)], 
	[has_volva(M)[source(hunterE)], 
	pale_brownish_cap(M)[source(hunterE)],
	patches(M)[source(hunterE)],
	cup_margin_lined(M)[source(hunterE)],
	~has_annulus(M)[source(hunterE)]
]) [rule_type(defeasible), context(any)].

pref(hunterE, [leader, hunterA, hunterB, hunterC, hunterD]).

/* Initial goals */

!start2.

/* Plans */

+!start2 : true <- .print("hello world from hunter E.").
