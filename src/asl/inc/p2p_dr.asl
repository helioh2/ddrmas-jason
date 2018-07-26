// Agent pdp_dr in project gold_miners

//{ include("p2p_dr_logic_base.asl") }

/* Initial goals */

!start.

/* Plans */

+!start : true <- .print("hello world from p2p_dr module.").

//
//+!p2p_dr(P) : true <- 
//		.print("Decided to catch ",P);
//		+P.

+!p2p_dr_front(P,C) : true <-
		.print("Aqui");
		?locally(P,C);
		.print("True");
		+P.
//		} else {
//			!p2p_dr(P,self,C);
//		}.

-!p2p_dr_front(P,C) : true <-
		.print("Aqui 2");
		!p2p_dr(P,self,C).
		
+!p2p_dr(P,C0,C): locally(P,C) <-
		 //se é provable pelas crenças locais (strict), acabou
		 .print("Achou locally. Respondendo para ",C0);
		 +provable(P,C,[]);
		.send(C0, tell, provable(P,C0,[C])).

+!p2p_dr(P,C0,C): .negate(P,Q) & locally(Q,C) <-
		 //se é provable pelas crenças locais (strict), acabou
		 .print("Achou locally oposto. Respondendo para ",C0);
		 +~provable(P,C,[]);
		.send(C0, tell, ~provable(P,C0,[C])).

+!p2p_dr(P,C0,C): not(locally(P,C)) & support_finished(P) & .negate(P,Q) & support_finished(Q) <-
//		+waiting_for_support_return(P,C,[],0);
		+waiting_p2p_response(P,C0);
		!return_to_caller(C,P).
		
+!p2p_dr(P,C0,C): not(locally(P,C)) & not(support_finished(P)) <-
			+waiting_p2p_response(P,C0);
			.print("Calling support for the literal. ",P);
			!support1(P,C);
			.negate(P,Q);
			.print("Calling support for negation. ",Q);
			!support1(Q,C).
			
+!support1(P,C): supportive_rule(_,C,P,_) <-
		for (supportive_rule(R,C,P,_)){
             +waiting_for_support_return(R,P,C,[],0);
             .print("Calling support for rule - ",R);
             !support1_aux(P,C,R);
             }.

-!support1(P,C): true <-
	+support_finished(P);
	.print("Support failed for ", P)
	!check_support_finished(P,C).


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
	        	.send(K, achieve, p2p_dr(B,C,K)); //A chamada a p2p_dr ao outro agente vai retornar provable para b1 se for. E se não for provable, retorna o que?
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

+provable(B,C,SS): context(C) & waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) <-
	.delete(B,Bs,NBs);
	-waiting_for_support_return(R,P,C,Bs,1);
	+waiting_for_support_return(R,P,C,NBs,1).
	

+~provable(B,K,SS): waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) <-  
	-waiting_for_support_return(R,P,C,Bs,1);
	+waiting_for_support_return(R,P,C,[],2).


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
	
	
+waiting_for_support_return(R,P,C,[],2): supportive_rule(R,C,P,_) <-
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
	};
	!check_support_finished(P,C).
	
	
+!check_support_finished(P,C): .negate(P,Q) & (support_finished(P) & support_finished(Q))  <-
	.print("Support finished for ", P);
	!return_to_caller(C,P).	

	
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
				+provable(P,C,SS);
				.send(C0, tell, provable(P,C0,[C]));
				.print("Aqui 12 - PROVABLE", P);
			} else {
				+~provable(P,C,SS);
				.send(C0, tell, ~provable(P,C0,[C]));
				.print("Aqui 12 - ~PROVABLE", P);
			};
		} else {
			+provable(P,C,SS);
			.send(C0, tell, provable(P,C0,[C]));
			.print("Aqui 12 - PROVABLE", P);
		};
		
	} else {
		+~provable(P,C,SS);
		.print("Aqui 12 - ~PROVABLE", P);
		.send(C0, tell, ~provable(P,C0,[C]));
	};
	-waiting_p2p_response(P,C0).


/* Rules: */

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

