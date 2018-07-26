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
		
//-!p2p_dr_front(P,C) : true <-
//		.print("Faiô!").

+!p2p_dr(P,C0,C): locally(P,C) <-
		 //se é provable pelas crenças locais (strict), acabou
		 .print("Achou locally. Respondendo para ",C0);
		.send(C0, tell, provable(P,C0,[C])).

+!p2p_dr(P,C0,C): .negate(P,Q) & locally(Q,C) <-
		 //se é provable pelas crenças locais (strict), acabou
		 .print("Achou locally oposto. Respondendo para ",C0);
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
			
//+!p2p_dr(P,C0,C): .negate(P,Q) & not(locally(P,C)) & not(support_finished(Q)) <-
////			+waiting_p2p_response(Q,C0);
//			
	
		

+!support1(P,C): supportive_rule(_,C,P,_) <-
		for (supportive_rule(R,C,P,_)){
             .print(R);
             +waiting_for_support_return(R,P,C,[],0);
             .print("Aqui 4");
             !support1_aux(P,C,R);
             }.

-!support1(P,C): true <-
	+support_finished(P);
	!check_support_finished(P,C).
	
//-!support1(P,C): true <-
//	.print("suppor error").

+!support1_aux(P,C,R): supportive_rule(R,C,P,Body) <-
		.print("Aqui 5");
		if (.empty(Body)) {
			?waiting_for_support_return(R,P,C,Current,_);
       		-+waiting_for_support_return(R,P,C,Current,1);
		} else {		
			for ( .member(B[source(K)], Body) ){
	             .print(B);
	             ?waiting_for_support_return(R,P,C,Current,_);
	             -+waiting_for_support_return(R,P,C,[B|Current],1);
	             };   
	        ?waiting_for_support_return(R,P,C,Current,_);
	        .print("Olha aí a merda: ",Current);
	        for (.member(B[source(K)], Body)){
	        	.print("Supporting ",B[source(K)])
	        	.send(K, achieve, p2p_dr(B,C,K)); //A chamada a p2p_dr ao outro agente vai retornar provable para b1 se for. E se não for provable, retorna o que?
	        	.print("Called support ",B[source(K)])
	        };
	             
        }.
       
         
//@locally_pos[atomic]
//+locally(B,K)[source(K)]:  waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) & C\==K <-
//		.print("Aqui 6");
//		+provable(B,C,[K]);
//		!decrease_waiting(R,P,C,Bs,1).

//@locally_neg[atomic]
//+locally(B,K)[source(K)]:  waiting_for_support_return(R,P,C,Bs,1) & .negate(B,Bn) & .member(Bn,Bs) <-
//		.print("Aqui derivou body negado.");
//		+~provable(Bn,C,[K]).


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
	

//@decrease_waiting[atomic]
//+!decrease_waiting(R,P,C,Bs,1): true <-
//	.delete(B,Bs,NBs);
//	-+waiting_for_support_return(R,P,C,NBs,1);
//	.print("Aqui 8 ",NBs).

//@not_provable[atomic]
+~provable(B,K,SS): waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) <-  
	-+waiting_for_support_return(R,P,C,[], 2).

//+waiting_for_support_return(R,[],1): true <-
//	.print("Retornou suporte Ok. Prosseguir. (JÁ VAI SER APPLICABLE RULE PELAS REGRAS)").
//	


//ACONTECE O SEGUINTE QUANDO TODOS OS BODY DE UMA REGRA SÃO SUPORTADOS:
+waiting_for_support_return(R,P,C,[],1): supportive_rule(R,C,P,Body) <-
	+provable(R,P,C,[]);
	.print("Literal: ",P);
	.print("Regra: ",R);
//	?provable(B,C,SSx);
//	.print("Body da regra:", Body);
//	.print("Support do body (fora): ", SSx);
	for (provable(B,C,SSx) & .member(B,Body)) {
		?provable(R,P,C,SSr);
		.print("Support da regra: ",SSr)
		.print("Support do body: ",SSx)
		.union(SSx,SSr,X);
		-+provable(R,P,C,X);
	};
	.print("Fez provable da regra ",R);
	
	?provable(R,P,C,SSr);
	.print("Support final da regra: ",SSr)
	if (not(provable(P,C,SS))) {	
		+provable(P,C,SSr);
	} else {
		//escolher mais forte
		?pref(C,T);
		if (provable(P,C,SS) & stronger(SSr,SS,T)) {
			-+provable(P,C,SSr);
		};
	};
	-+waiting_for_support_return(R,P,C,[],2).
	
	
+waiting_for_support_return(R,P,C,[],2): supportive_rule(R,C,P,_) <-
	.print("Aqui 9", R);
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
	.print("Aqui 11");
	!return_to_caller(C,P).	

	
+!check_support_finished(P,C):  .negate(P,Q) & not(support_finished(P) & support_finished(Q)) <- true.
	
//+waiting_for_support_return(R,P,C,[],2): not(support_finished(P) 	

+!return_to_caller(C,P): .negate(P,Q) & waiting_p2p_response(Q,C0) & not(waiting_p2p_response(P,C0)) <-
	!return_to_caller_aux(C,Q,C0).

+!return_to_caller(C,P): waiting_p2p_response(P,C0) <-
	!return_to_caller_aux(C,P,C0).	

+!return_to_caller_aux(C,P,C0): true <-
	?pref(C,T);
	if (provable(P,C,SS)) {
		.negate(P,Q);
		if (provable(Q,C,SSn)) {
			if (not(stronger(SSn,SS,T))) {
				.send(C0, tell, provable(P,C0,[C]));
				.print("Aqui 12 - PROVABLE", P);
			} else {
				.send(C0, tell, ~provable(P,C0,[C]));
				.print("Aqui 12 - ~PROVABLE", P);
			};
		} else {
			.send(C0, tell, provable(P,C0,[C]));
			.print("Aqui 12 - PROVABLE", P);
		};
		
	} else {
		.print("Aqui 12 - ~PROVABLE", P);
		.send(C0, tell, ~provable(P,C0,[C]));
	};
	-waiting_p2p_response(P,C0).
	

//+applicable_rule(R,C,X,L,SSr) :  pref(C,T) & chosen_applicable_rule(S,C,X,_,SSs) 
//									& R\==S & stronger(SSr,SSs,T,SSr) <-
//	+chosen_applicable_rule(R,C,X,L,SSr).
//
//+applicable_rule(R,C,X,L,SSr) : not(chosen_applicable_rule(S,C,X,_,SSs)) & R\==S <-
//	+chosen_applicable_rule(R,C,X,L,SSr).


//+!support(C0,lit(P,C),SS): supportive_rule(R,C1,P,B) <-
//	.send(C1, achieve, p2p_dr(P,C0,C,SSr) )

/* Rules: */

//rules_with_head(X, [R1|RR]) :- .print("r1") & not_strict_supportive_rule(R1,C,X,B) & rules_with_head(X, RR).
//rules_with_head(X, []) :- .print("r2") & true.


supportive_rule(Name,Context,Head,Body) :- .print("r3") & strict_rule(Name,Context,Head,Body).
supportive_rule(Name,Context,Head,Body) :- .print("r4") & defeasible_rule(Name,Context,Head,Body).
supportive_rule(Name,Context,Head,Body) :- .print("r5", Head) & mapping_rule(Name,Context,Head,Body).
not_strict_supportive_rule(Name,Context,Head,Body) :- .print("r6") & supportive_rule(Name,Context,Head,Body) & not(strict_rule(Name,Context,Head,Body)).

locally(X,C) :- .print("r7") & strict_rule(R,C,X,L) & locally_provable(L,C). //locally se é strict e corpo é locally_provable em C

locally_provable([],C) :- .print("r8") & true.  //lista vazia sempre é locally_provable (caso base)
locally_provable([X1|X2],C) :- .print("r9") & locally(X1,C) & locally_provable(X2,C). //uma lista de literais é locally_provable se cada item é locally

//provable(X,C,[]) :- .print("r10") & locally(X,C).  //se é locally então é provable com SSr = []



//!!!
//provable(X,C,SSr) :- .print("r11") & chosen_applicable_rule(R,C,X,L,SSr) & not(locally(~X, C)) & not(blocked(R,C,X,SSr)).
//senão, deve haver uma applicable_rule, a negação não pode ser provable locally, e X não é blocked em C


//provable(X,C,[K]) :- .print("r12") & provable(X,K,SSx) & (K\==C).
// se X é provable em um context K !!!QUALQUER!!!, então também é provable em C, adicionando-se ainda
// K ao SS
//!!!


//applicable_rule(R,C,X,L,SSr) :- .print("r13") & supportive_rule(R,C,X,L) & provable_list(L,C,SSr).
//// se R é supportive e corpo da regra é provable_list em C, então é applicable rule
//
//provable_list([],C,[]) :- .print("r14") & context(C).  //caso base
//provable_list([X1|X2],C,SSL) :- .print("r15") & provable(X1,C,SS1) &  provable_list(X2,C,SS2) & .union(SS1,SS2,SSL).
//// uma lista de literais (corpo de uma regra) é provable_list em C se cada literal é provable em C
//// tal que seu SS será a união dos SS de cada literal
//
//blocked(R,C,X,SSr) :- .print("r16") & applicable_rule(S,C,~X,L,SSs) & pref(C,T) & not(stronger(SSr,SSs,T)).
// um literal X é bloqueado em C em relação a uma regra R se existe outra regra aplicável (S) 
// que conclui a negação de X, e o SS da regra R não é mais forte que o SS da regra S de acordo
// com as preferências (T) de C.

//chosen_applicable_rule(R,C,C,L,SSr) :- applicable_rule(S,C,X,L,SSs) & stronger()

//rank_aux([X|Tail],T,[Pos|TailPos]) :- .nth(Pos,T,X) & rank_aux(Tail,T,TailPos).
//rank_aux([],T,_).
//
//rank(SS,T,R) :- rank_aux(SS,T,X) & R=.max(X).
//stronger(A,B,T) :- myLib.rank(A,T,RA) & myLib.rank(B,T,RB) & RA<RB.



//
stronger(A,B,T,B) :- .print("r17") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,A1).
stronger(A,B,T,A) :- .print("r18") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,B1).
weakest([X],X,_) :- true.
weakest([X|Tail],M,T) :- .print("r20") & weakest(Tail,M1,T) & weaker(X,M1,T,M).
weaker(Y1,Y2,T,Y1) :- .print("r21") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos1>Pos2.
weaker(Y1,Y2,T,Y2) :- .print("r22") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos2>Pos1.


//+!p2p_dr(P, _, _) : analysing_mushroom & P  //when it is local inferred
//	<- 		P .
//	
//+!p2p_dr(P, Hist) : analysing_mushrrom & not P
//    <- !support(P, Hist).
    
//+!support(P, Hist): 

