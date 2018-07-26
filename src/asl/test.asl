// Agent test in project ex3_bikakis

/* Initial beliefs and rules */

context(test).

supportive_rule(r11, test, pos(a)[source(test)], [pos(b)[source(peerC)]] ).
supportive_rule(r12, test, neg(c)[source(test)], [pos(b)[source(peerC)]] ).

pos(X) :- context(C) & supportive_rule(_,_,pos(X)[source(C)],_).
neg(X) :- context(C) & supportive_rule(_,_,neg(X)[source(C)],_).

lit(m).
~lit(n).

//support_finished(lit(b)).

/* Initial goals */

!start(~lit(n)).


/* Plans */

+?pos(X): pos(X) <-
	true.
+?pos(X): neg(neg(X)) <-
	true.
+?neg(X): neg(X) <-
	true.
+?neg(X): pos(neg(X)) | neg(pos(X)) <-
	true.


+!start(X) : true <- 
	?X;
	.negate(X,Y);
	.print("hello world.", Y);
	+Y.
	
+lit(n): true <- .print("Inverteu").
