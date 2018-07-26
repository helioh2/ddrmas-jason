// Agent pdp_dr in project gold_miners

/* Initial beliefs and rules */


/* Initial goals */

!start.

/* Plans */

+!start : true <- .print("hello world from p2p_dr module.").


+!p2p_dr(P) : true <- 
		.print("Decided to catch ",P);
		+P.

+!p2p_dr_front(P,C) : true <-
		.print("Aqui");
		!p2p_dr(P,self,C);
		if (provable(lit(P,C),C)) {
			.print("True");
			+P;
		}.
		
-!p2p_dr_front(P,C) : true <-
		.print("Faiô!").

+!p2p_dr(P,C0,C): true <-
		?provable(lit(P,C),C,SS);  //se é provable pelas crenças locais (strict), acabou
		.send(C0, tell, provable(lit(P,C),C,SS)).

+!p2p_dr(P,C0,C): not(provable(lit(P,C),C,_)) <-
//		+waiting_for_support_return(P,C,[],0);
		!support1(lit(P,C)).
		

+!support1(lit(P,C)): rules_with_head(P,Rules) <-
		for ( .member(R, Rules) ){
             .print(R);
             +waiting_for_support_return_(R,P,C,[],0);
             !support1_aux1(P,C,R)
             }.
+!support1_aux(P,C,R): not_strict_supportive_rule(R,C,P,Body) <-
		for ( .member(B, Body) ){
             .print(B);
             .send(source(B), achieve, p2p_dr(B,C,source(B))); //A chamada a p2p_dr ao outro agente vai retornar provable para b1 se for. E se não for provable, retorna o que?
             -waiting_for_support_return(R,P,C,Current,_);
             +waiting_for_support_return(R,P,C,[B|Current],1);
             }.

//A seguir é a resposta do P2P_DR chamado do outro agente:
+provable(lit(B,K),K,SS): waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) <-
	-waiting_for_support_return(R,P,C,Bs,1);
	.delete(B,Bs,NBs);
	+waiting_for_support_return(R,P,C,NBs,1).
	
+~provable(lit(B,K),K,SS): waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) <-
	-waiting_for_support_return(R,Bs, 1);
	+waiting_for_support_return(R,[], 2).

//+waiting_for_support_return(R,[],1): true <-
//	.print("Retornou suporte Ok. Prosseguir. (JÁ VAI SER APPLICABLE RULE PELAS REGRAS)").
//	

+waiting_for_support_return(R,P,C,[],St): rules_with_head(P,Rules) & St > 0 <-
//	.print("Um dos body nao deu. Deixa quieto");
	+support_finished(P);
	for ( .member(S, Rules) ){
		if (waiting_for_support_return(S,P,C,Bs,Status) & (not(.empty(Bs)) | Status == 0)) {
			-support_finished(P);
		};
	};
	if (support_finished(P)) {
		!return_to_caller(C,P);
		-support_finished(P);
	}.
	
+!return_to_caller(C,P): true <-
	if (provable(lit(P,K),K,SS)) {
		.send(C, tell, provable(lit(P,K),K,SS));
	} else {
		.send(C, tell, ~provable(lit(P,K),K,SS));
	}.
	

+applicable_rule(R,C,X,L,SSr) :  pref(C,T) & chosen_applicable_rule(S,C,X,_,SSs) 
									& R\==S & stronger(SSr,SSs,T,SSr) <-
	+chosen_applicable_rule(R,C,X,L,SSr).

+applicable_rule(R,C,X,L,SSr) : not(chosen_applicable_rule(S,C,X,_,SSs)) & R\==S <-
	+chosen_applicable_rule(R,C,X,L,SSr).


//+!support(C0,lit(P,C),SS): supportive_rule(R,C1,P,B) <-
//	.send(C1, achieve, p2p_dr(P,C0,C,SSr) )

/* Rules: */

rules_with_head(X, [R1|RR]) :- not_strict_supportive_rule(R1,C,X,B) & rules_with_head(X, RR).
rules_with_head(X, []) :- not_strict_supportive_rule(_,_,X,_).

supportive_rule(Name,Context,Head,Body) :- strict_rule(Name,Context,Head,Body).
supportive_rule(Name,Context,Head,Body) :- defeasible_rule(Name,Context,Head,Body).
supportive_rule(Name,Context,Head,Body) :- mapping_rule(Name,Context,Head,Body).
not_strict_supportive_rule(Name,Context,Head,Body) :- supportive_rule(Name,Context,Head,Body) & not(strict_rule(Name,Context,Head,Body)).
locally(lit(X,C),C) :- strict(R,C,X,L) & locally_provable(L,C). //locally se é strict e corpo é locally_provable em C

locally_provable([],C) :- context(C).  //lista vazia sempre é locally_provable (caso base)
locally_provable([X1|X2],C) :- locally(lit(X1,C),C) & locally_provable(X2,C). //uma lista de literais é locally_provable se cada item é locally

provable(X,C,[]) :- locally(X,C).  //se é locally então é provable com SSr = []



//!!!
provable(X,C,SSr) :- chosen_applicable_rule(R,C,X,L,SSr) & not(locally(~X, C)) & not(blocked(R,C,X,SSr)).
//senão, deve haver uma applicable_rule, a negação não pode ser provable locally, e X não é blocked em C


provable(lit(X,K),C,[K]) :- provable(lit(X,K),K,SSx) & (K\==C).
// se X é provable em um context K !!!QUALQUER!!!, então também é provable em C, adicionando-se ainda
// K ao SS
//!!!


applicable_rule(R,C,X,L,SSr) :- supportive_rule(R,C,X,L) & provable_list(L,C,SSr).
// se R é supportive e corpo da regra é provable_list em C, então é applicable rule

provable_list([],C,[]) :- context(C).  //caso base
provable_list([X1|X2],C,SSL) :- provable(X1,C,SS1) &  provable_list(X2,C,SS2) & .union(SS1,SS2,SSL).
// uma lista de literais (corpo de uma regra) é provable_list em C se cada literal é provable em C
// tal que seu SS será a união dos SS de cada literal

blocked(R,C,X,SSr) :- applicable_rule(S,C,~X,L,SSs) & pref(C,T) & not(stronger(SSr,SSs,T)).
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
stronger(A,B,T,B) :- weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,A1).
stronger(A,B,T,A) :- weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,B1).
weakest([X],X,_) :- true.
weakest([X|Tail],M,T) :- weakest(Tail,M1,T) & weaker(X,M1,T,M).
weaker(Y1,Y2,T,Y1) :- .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos1>Pos2.
weaker(Y1,Y2,T,Y2) :- .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos2>Pos1.


//+!p2p_dr(P, _, _) : analysing_mushroom & P  //when it is local inferred
//	<- 		P .
//	
//+!p2p_dr(P, Hist) : analysing_mushrrom & not P
//    <- !support(P, Hist).
    
//+!support(P, Hist): 

