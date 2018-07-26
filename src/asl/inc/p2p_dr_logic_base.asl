// Agent test in project ex3_bikakis

/* Initial beliefs and rules */

has_literal(X) :- context(C) & supportive_rule(_,_,X[source(C)],_).


/* Plans */

//+?pos(X): pos(X) <-
//	true.
//+?pos(X): neg(neg(X)) <-
//	true.
//+?neg(X): neg(X) <-
//	true.
//+?neg(X): pos(neg(X)) | neg(pos(X)) <-
//	true.

