// Agent pdp_dr in project gold_miners

//{ include("p2p_dr_logic_base.asl") }

rule_id(1).

/* Initial goals */

!start.

/* Plans */

+!start : true <- .print("hello world from p2p_dr module.").

+!p2p_dr_front(P,C) : true <-
		.print("Aqui");
		?locally(P,C);
		.print("True");
		+P.

-!p2p_dr_front(P,C) : true <-
		.print("Aqui 2");
		!p2p_dr(P,self,C).
		
+!p2p_dr(P,C0,C): locally(P,_) <-
		 //se é provable pelas crenças locais (strict), acabou
		 .print("Achou locally. Respondendo para ",C0);
//		 +provable(P,C,[]);
		.send(C0, tell, provable(P,C0,[C])).

+!p2p_dr(P,C0,C): .negate(P,Q) & locally(Q,_) <-
		 //se é provable pelas crenças locais (strict), acabou
		 .print("Achou locally oposto. Respondendo para ",C0);
//		 +~provable(P,C,[]);
		.send(C0, tell, ~provable(P,C0,[C])).

+!p2p_dr(P,C0,C): not(locally(P,_)) & support_finished(P) & .negate(P,Q) & support_finished(Q) <-
//		+waiting_for_support_return(P,C,[],0);
		+waiting_p2p_response(P,C0);
		!return_to_caller(C,P).
		
+!p2p_dr(P,C0,C): not(locally(P,_)) & not(support_finished(P)) <-
		+waiting_p2p_response(P,C0);
		.print("Calling support for the literal. ",P);
		!support1(P,C).

+!p2p_dr_with_percepts(P,C0,C,Ps): true <-
//		+asked_for_from(P,C0);
		+percepts(P,C0,Ps);
		!p2p_dr(P,C0,C).

+!p2p_dr_helping(P,C0,C,Ps): true <-
		+asked_for_from(P,C0);
		+percepts(P,C0,Ps);
		!p2p_dr(P,C0,C).
		
+!p2p_dr_helping(P,C0,C): true <-
		+asked_for_from(P,C0);
		!p2p_dr(P,C0,C).
			
+!support1(P,C): supportive_rule(_,C,P,_) <-
		for (supportive_rule(R,C,P,_)){
             +waiting_for_support_return(R,P,C,[],0);
             .print("Calling support for rule - ",R);
             !support1_aux(P,C,R);
        }.

-!support1(P,C): true <-
		+support_finished(P);
		.print("Support failed for ", P);
		+waiting_for_support_return(R,P,C,[],2).
	//	!check_support_finished(P,C).

//+!support1(P[source(X)],C): X==any & not(asked_for_from(P,_)) & 
//					(not(supportive_rule(_,C,P,_)) | 
//						(not(provable(P,C,_)) & not(checked_context_for(P,_)))
//					)  <-
//		for (known_context(K)) {
//			+checked_context_for(P,C,K);
//			if (percepts(P,C0,Ps)) {
//				.send(K, achieve, p2p_dr_helping(P,C,K,Ps));
//			} else {
//				.send(K, achieve, p2p_dr_helping(P,C,K));
//			};
//		}.
	
+!support1_aux(P,C,R): supportive_rule(R,C,P,Body) <-
		.print("Trying support for rule ", R);
		if (.empty(Body)) {
			?waiting_for_support_return(R,P,C,Current,_);
       		-+waiting_for_support_return(R,P,C,Current,1);
		} else {		
			for ( .member(B, Body) ){
	             .print("Adding body item:", B);
	             ?waiting_for_support_return(R,P,C,Current,_);
	             -+waiting_for_support_return(R,P,C,[B|Current],1);
	        };   
	        ?waiting_for_support_return(R,P,C,Current,_);
	        for (.member(B[source(K)], Body)){
	        	.print("Asking support for ",B[source(K)]) 
	        	if (K==any) {
	        		!ask_all_known_contexts(P,C,B);
	        	} else {       
	        		if (percepts(P,_,Ps) & K\==C) {
						.send(K, achieve, p2p_dr_with_percepts(B,C,K,Ps));
					} else {
						.send(K, achieve, p2p_dr(B,C,K));
		};	
	        	}
	        };
	             
        }.

+!ask_all_known_contexts(P,C,B) : true <-
	for (known_context(K)) {
		+waiting_for_support_from_context(B,K);
		if (percepts(P,_,Ps)) {
			.send(K, achieve, p2p_dr_with_percepts(B,C,K,Ps));
		} else {
			.send(K, achieve, p2p_dr(B,C,K));
		};
	}.


//A seguir é a resposta do P2P_DR chamado do outro agente:
//@provable[atomic]
//+provable(B,K,SS): not(context(K)) & waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) <-	
////	-provable(B,K,SS);	
//	-+provable(B,C,[K]);
	
//	-provable(B,K,SS);
//	.print("Aqui 7 ",Bs);
//	!decrease_waiting(R,P,C,Bs,1).
	
//	.print("Aqui 8 ",NBs).
//
//+provable(P,K,SS): context(C) & checked_context_for(P,C,K) <- 
//	-checked_context_for(P,C,K).
//	
//+~provable(P,K,SS): context(C) & checked_context_for(P,C,K) <- 
//	-checked_context_for(P,C,K).

@pv1[atomic]
+provable(B,C,SS)[source(K)]: context(C) & waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) & not(waiting_for_support_from_context(B,K)) <-
	.delete(B,Bs,NBs);
	-waiting_for_support_return(R,P,C,Bs,1);
	+waiting_for_support_return(R,P,C,NBs,1).
	
@pv2[atomic]
+~provable(B,C,SS)[source(K)]: waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) & not(waiting_for_support_from_context(B,K)) <-  
	-~provable(B,C,SS)[source(K)];
	-waiting_for_support_return(R,P,C,Bs,1);
	+waiting_for_support_return(R,P,C,[],2).

@pv3[atomic]	
+~provable(B,C,SS)[source(K)]: context(C) & waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) & waiting_for_support_from_context(B,K) <-
	-~provable(B,C,SS)[source(K)];
	!evaluate_from_many_contexts(B,K).
	
@pv4[atomic]
+provable(B,C,SS)[source(K)]: context(C) & waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) & waiting_for_support_from_context(B,K) <-
	!evaluate_from_many_contexts(B,K).

@pvaux[atomic]
+!evaluate_from_many_contexts(B,K) : waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) <-
	-waiting_for_support_from_context(B,K);
	if (not(waiting_for_support_from_context(B,_))) {
		-waiting_for_support_return(R,P,C,Bs,1);
		if (not(provable(B,_,SS))) {  //se tem algum provable
			+waiting_for_support_return(R,P,C,[],2);
		} else { 
			.delete(B,Bs,NBs);
			+waiting_for_support_return(R,P,C,NBs,1);
		};
		
	}.

//ACONTECE O SEGUINTE QUANDO TODOS OS BODY DE UMA REGRA SÃO SUPORTADOS:
+waiting_for_support_return(R,P,C,[],1): supportive_rule(R,C,P,Body) <-
	+applicable_rule(R,P,C,[]);
	.print("All items of body of rule", R);
	.print("Literal: ",P);
	for (provable(B,C,SSx) & .member(B,Body)) {
		?applicable_rule(R,P,C,SSr);
		.union(SSx,SSr,X);
		-+applicable_rule(R,P,C,X);
	};
	.print("Fez provable da regra ",R);
	
	?applicable_rule(R,P,C,SSr);
	.print("Support final da regra: ",SSr)
	if (not(supported(P,C,SS))) {	
		+supported(P,C,SSr);
	} else {
		//escolher mais forte
		?pref(C,T);
		if (supported(P,C,SS) & stronger(SSr,SS,T)) {
			-supported(P,C,SS);
			+supported(P,C,SSr);
		};
	};
	-waiting_for_support_return(R,P,C,[],1);
	+waiting_for_support_return(R,P,C,[],2).
	
	
+waiting_for_support_return(R,P,C,[],2): true <- //supportive_rule(R,C,P,_) <-
	.print("Found provable or not for " , R);
	-waiting_for_support_return(R,P,C,[],_);
	+support_finished_aux(P);
	for (waiting_for_support_return(S,P,C,Bs,Status) & (Status < 2)) {
		.print("Aqui 10 - support não terminado", S);
		-support_finished_aux(P);		
	};
	if (support_finished_aux(P)) {
		+support_finished(P);
		-support_finished_aux(P);	
		if (not(supported(P,C,_))) {
			!return_to_caller(C,P);
		} else {
			!check_support_finished(P,C);
		};		
	}.

	
+!check_support_finished(P,C): .negate(P,Q) & (support_finished(P) & support_finished(Q))  <-
	.print("Support finished for ", P);
	!return_to_caller(C,P).	

+!check_support_finished(P,C): .negate(P,Q) & support_finished(P) & not(support_finished(Q)) <-
	.print("Calling support for negation. ",Q);
	!support1(Q,C).
	
+!check_support_finished(P,C):  .negate(P,Q) & not(support_finished(P) & support_finished(Q)) <- true.
	
//+waiting_for_support_return(R,P,C,[],2): not(support_finished(P) 	

+!return_to_caller(C,P): .negate(P,Q) & waiting_p2p_response(Q,C0) & not(waiting_p2p_response(P,C0)) <-
	!return_to_caller_aux(C,Q,C0).

+!return_to_caller(C,P): waiting_p2p_response(P,C0) <-
	!return_to_caller_aux(C,P,C0).	

+!return_to_caller_aux(C,P,C0): true <-
	?pref(C,T);
	if (supported(P,C,SS)) {
		.negate(P,Q);
		if (supported(Q,C,SSn)) {
			if (not(stronger(SSn,SS,T))) {
//				+provable(P,C,SS);
				.send(C0, tell, provable(P,C0,[C]));
				.print("Aqui 12 - PROVABLE", P);
			} else {
//				+~provable(P,C,SS);
				.send(C0, tell, ~provable(P,C0,[C]));
				.print("Aqui 12 - ~PROVABLE", P);
			};
		} else {
//			+provable(P,C,SS);
			.send(C0, tell, provable(P,C0,[C]));
			.print("Aqui 12 - PROVABLE", P);
		};
		
	} else {
//		+~provable(P,C,SS);
		.print("Aqui 12 - ~PROVABLE", P);
		.send(C0, tell, ~provable(P,C0,[C]));
	};
	!clear(C,P,C0);
	-waiting_p2p_response(P,C0).

+!clear(C,P,C0) : true <-
	-waiting_p2p_response(P,C0);
//	-strict_rule(_,C0,_,_).
	for (strict_rule(R,C0,L,_)) {
		-strict_rule(R,C0,L,_);  //esquecimento??
	}.

+percepts(P,C,Ps): true <-
	for (.member(L,Ps)) {
		if (not(strict_rule(_,_L,_))) {
			?rule_id(IDN);
			.concat("tr",IDN,ID);
			-+rule_id(IDN+1);
			+strict_rule(ID,C,L,[]);		
		}
	}.

/* Rules: */

known_context(A) :- pref(C,T) & .member(A,T).
strict_rule(Name,Context,Head[source(Context)],[]) :- percept(Name, Context, Head).
//strict_rule(Name,Context,Head[source(Context)],[]) :- .print("Adding percept locally") & percepts(Lit, Context, Heads) & .member(Head,Heads).

supportive_rule(Name,Context,Head,Body) :- .print("r3") & strict_rule(Name,Context,Head,Body).
supportive_rule(Name,Context,Head,Body) :- .print("r4") & defeasible_rule(Name,Context,Head,Body).
supportive_rule(Name,Context,Head,Body) :- .print("r5 ", Head) & mapping_rule(Name,Context,Head,Body).
not_strict_supportive_rule(Name,Context,Head,Body) :- .print("r6") & supportive_rule(Name,Context,Head,Body) & not(strict_rule(Name,Context,Head,Body)).

locally(X,C) :- .print("r7") & strict_rule(R,C,X,L) & locally_provable(L,C). //locally se é strict e corpo é locally_provable em C

locally_provable([],C) :- .print("r8") & true.  //lista vazia sempre é locally_provable (caso base)
locally_provable([X1|X2],C) :- .print("r9") & locally(X1,C) & locally_provable(X2,C). //uma lista de literais é locally_provable se cada item é locally

stronger(A,B,T,B) :- .print("r17") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,A1).
stronger(A,B,T,A) :- .print("r18") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,B1).
weakest([X],X,_) :- true.
weakest([X|Tail],M,T) :- .print("r20") & weakest(Tail,M1,T) & weaker(X,M1,T,M).
weaker(Y1,Y2,T,Y1) :- .print("r21") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos1>Pos2.
weaker(Y1,Y2,T,Y2) :- .print("r22") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos2>Pos1.

