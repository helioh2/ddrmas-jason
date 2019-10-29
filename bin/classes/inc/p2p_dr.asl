rule_id(1).
context_id(1).

/* Initial goals */

!start.

/* Plans */

+!new_query_context(ID): true <-
	?context_id(IDN);
	.concat("c", IDN, ID);
	-+context_id(IDN+1);
	+context(ID).

+!pack_focus_rules(Rf): true <-
	.findall(rule(R,A,H,B)[rule_type(T), context(CId)], focus_rule(R,A,H,B)[rule_type(T)], Rf).

+!start : true <- .print("hello world from query module.").


/* Planos de aÃ§Ã£o de consulta incluindo foco */
+!query_with_focus_rules(CId,P,Rf)[source(A0)]: true <-
	+focus_rules(CId,Rf);
	!query(CId,P)[source(A0)].

+focus_rules(CId,Rf) : true <-
	for (.member(R, Rf)) { +R; }.
		
//+focus_rules(CId, RfH, RfB, RfT, Q) : true <-
//		for (.range(I, 0, Q-1)) {
//			.nth(I, RfH, H);
//			.nth(I, RfB, B);
//			.nth(I, RfT, T);
//			if (not(rule(_,_,H,B)[context(CId), rule_type(T)])) {
//				?rule_id(IDN);
//				.concat("tr",IDN,ID);
//				-+rule_id(IDN+1);
//				?agent(A);
//				+rule(ID,A,H,B)[context(CId), rule_type(T)];	
//			}
//		}.


/* Planos de aÃ§Ã£o: busca local	*/
+!query(CId,P)[source(A0)]: locally(CId,P) <-
	 //se Ã© provable pelas crenÃ§as locais (strict), acabou
	 .print("Achou locally ", P);
	 +query_context(CId,A0,P);		 
	 +provable(P,[])[context(CId)];
	 !return_to_caller(CId,P). 

+!query(CId,P)[source(A0)]: .negate(P,Q) & locally(CId,Q) <-
	 //se Ã© provable pelas crenÃ§as locais (strict), acabou
	 .print("Achou locally oposto ",Q);
	 +query_context(CId,A0,P);	
	 +~provable(P,[])[context(CId)];
	 !return_to_caller(CId,P).

/* Planos de aÃ§Ã£o: busca suporte */
+!query(CId,P)[source(A0)]: not(locally(CId,P)) & support_finished(CId,P) & .negate(P,Q) & support_finished(CId,Q) <-
	+query_context(CId,A0,P);
	!return_to_caller(A,P).

//+!query(CId,P,A0): supported(P,A,_) <-
//		+query_context(CId,A0);
//		+waiting_p2p_response(P,A0,Z); //???
//		!return_to_caller(A,P).

+!query(CId,P)[source(A0)]: not(locally(CId,P)) & not(support_finished(CId,P)) <-
		+query_context(CId,A0,P);
		.print("Calling support for the literal. ",P);
//		+waiting_support_for(CId, P);  //!!! DESENVOLVER FORMA DE EVITAR SUPPORTS ATROPELADOS PARA O MESMO CARA.
		!support(CId,P).
//		.negate(P,Q);
//		!support(CId,P);
//		!support(CId,Q).

/* Planos de aÃ§Ã£o: suporte	*/		
+!support(CId,P): rule(_,_,P,_)[context(C)] & (C == Cid | C == any) <-
	for (rule(R,_,P,Body)[context(C)] & (C == Cid | C == any)){
		+waiting_for_support_return(CId,R,P,Body,1);
	    for (.member(B[source(Ag)], Body)){
	    	!evaluate_body_member(CId,B,Ag);
	    };            
    }.

-!support(CId,P): true <-
	+support_finished(P);
	+~provable(P,[])[context(CId)];
	.print("Support failed for ", P);
	!return_to_caller(CId, P).

+!evaluate_body_member(CId,B,Ag): Ag == any <-
	!ask_all_known_agents(CId,B).
	
+!evaluate_body_member(CId,B,Ag): .my_name(Me) & (Ag == Me | Ag == self) <-
	!query(CId,B)[source(Me)].

+!evaluate_body_member(CId,B,Ag): .my_name(Me) & Ag \== any & Ag \== Me & Ag \== self  <-
	!ask_other_agent(CId,B,Ag).

/* Consulta aos agentos conhecidos */
+!ask_all_known_agents(CId,B): true <-
	.findall(Ag, known_agent(Ag), L);
	if (not(query_context(CId,_,B))) {
		.my_name(Me);
		.send(Me, achieve, query(CId,B));
		+waiting_for_support_from_arbitrary_agents(CId,B,[Me|L]);  //talvez otimizar usando somente contagem
	} else {
		+waiting_for_support_from_arbitrary_agents(CId,B,L); 
	}
    !ask_other_agent(CId,B,L).

+!ask_other_agent(CId,B,Ag): focus_rules(CId,Rf) <-
	.send(Ag, achieve, query_with_focus_rules(CId,B,Rf)).
		
+!ask_other_agent(CId,B,Ag): not(focus_rules(CId,Rf)) <-
	.send(Ag, achieve, query(CId,B)).


/* Planos de aÃ§Ã£o para tratamento de resposta Ã s consultas */

/* Este plano Ã© disparado quando chega uma resposta de consulta (provable para B) feita especificamente para K
   B Ã© entÃ£o removido da lista de termos do waiting_for_support_return  */
   
@pv1[atomic]
+provable(B,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,B,L)) <-
	.delete(B,Bs,NBs);
	-waiting_for_support_return(CId,R,P,Bs,1);
	+waiting_for_support_return(CId,R,P,NBs,1);
	-+provable(B, SS)[source(Ag), context(CId), chosen_to_support(P)].


/* Este plano Ã© disparado quando chega uma resposta de consulta (nÃ£o provable para B) feita especificamente para K	
   A lista de termos do waiting_for_support_return Ã© entÃ£o esvaziada (pois se um termo nÃ£o Ã© provable, jÃ¡ invalida a regra) */
@pv2[atomic]
+~provable(B,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,B,L)) <-  
	-waiting_for_support_return(CId,R,P,Bs,1);
	+waiting_for_support_return(CId,R,P,[],2) .


/* Os trÃªs planos a seguir tratam as respostas das concultas no caso de um termo ter sido 
   consultado a vÃ¡rios agentos (any)
   O raciocÃ­nio sÃ³ segue quando todos os agentos responderem. */

@pv4[atomic]
+provable(B,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,1) 
		& .member(B,Bs) 
		& waiting_for_support_from_arbitrary_agents(CId,B,L) <-
	!evaluate_from_many_agents(B,Ag).   
   
@pv3[atomic]	
+~provable(B,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,1) 
		& .member(B,Bs) 
		& waiting_for_support_from_arbitrary_agents(CId,B,L) <-
	!evaluate_from_many_agents(B,Ag).   
	

@pvaux[atomic]
+!evaluate_from_many_agents(B,Ag) : 
		waiting_for_support_return(CId,R,P,Bs,1)
		& .member(B,Bs) 
		& waiting_for_support_from_arbitrary_agents(CId,B,L)  <-
	if (Ag == self) {
		.my_name(Me);
		.delete(Me, L, NL);
	} else {
		.delete(Ag, L, NL);
	}
	
	-waiting_for_support_from_arbitrary_agents(CId,B,L);
	+waiting_for_support_from_arbitrary_agents(CId,B,NL);
	!evaluate_from_many_agents_when_everyone_answered(B,Ag).
	
+!evaluate_from_many_agents_when_everyone_answered(B,Ag):
		waiting_for_support_from_arbitrary_agents(CId,B,NL)	& .empty(NL)
		& ~provable(B,SS)[context(CId)] <-
	-waiting_for_support_from_arbitrary_agents(CId,B,NL); 
	-waiting_for_support_return(CId,R,P,Bs,1);
	+waiting_for_support_return(CId,R,P,[],2).
	
+!evaluate_from_many_agents_when_everyone_answered(B,Ag):
		waiting_for_support_from_arbitrary_agents(CId,B,NL)	& .empty(NL)
		& provable(B,SS)[context(CId)] <-
	-waiting_for_support_from_arbitrary_agents(CId,B,NL);
	.findall(provable(B,SS)[source(Ag), context(CId)], provable(B,SS)[source(Ag), context(CId)], Ans);
	!find_strongest(Ans, provable(WB,WSS)[source(WAg), context(CId)]);
//	-+provable(WB, WSS)[source(WAg), context(CId)];
	-+provable(WB, WSS)[source(WAg), context(CId), chosen_to_support(P)];  //!!
	.delete(B,Bs,NBs);
	-waiting_for_support_return(CId,R,P,Bs,1);
	+waiting_for_support_return(CId,R,P,NBs,1).		

-!evaluate_from_many_agents_when_everyone_answered(B,Ag): true .

+!find_strongest(L,W): true <-
	+strongest_sup_set(0);
	+strongest(0);
	for (.member(X,L) & X = provable(B,SS)) { //!!!
		?strongest_sup_set(SSw);
		?pref(T);
		if (SSw == 0 | stronger(SS, SSw, T)) {
			-+strongest_sup_set(SS);
			-+strongest(X);
		}
	};
	?strongest(X);
	W = X.

/* O plano de aÃ§Ã£o a seguir Ã© disparado quando todos os termos do corpo da regra R
   Ã© avaliado e nenhum ~provable foi encontrado (flag 1)  */
@apprule
+waiting_for_support_return(CId,R,P,[],1): 
		rule(R,_,P,Body)[context(C)] & (C == Cid | C == any) <-
	+applicable_rule(R,P,[]);
	.print("--- Regra aplicÃ¡vel encontrada para: ", P);
	.print("Regra: ", R);
	for (provable(B, SSx)[source(Ag), context(CId), chosen_to_support(P)] & .member(B,Body)) {
		?applicable_rule(R,P,SSr);
		!update_applicable_rule(R,P,SSr,Ag,SSx);
	};
	?applicable_rule(R,P,SSr);
	.print("Supportive set final da regra: ",SSr);
	!check_supported(R,P,SSr);
	-waiting_for_support_return(R,P,A,[],1);
	+waiting_for_support_return(R,P,A,[],2).

+!update_applicable_rule(R,P,SSr,Ag,SSx): 
		applicable_rule(R,P,SSr) 
		& .my_name(Me) 
		& Ag == Me <-
	.union(SSr, SSx, SS);
	-+applicable_rule(R,P,SS).
	
+!update_applicable_rule(R,P,SSr,Ag,SSx): 
		applicable_rule(R,P,SSr) 
		& .my_name(Me) 
		& Ag \== Me <-
	-+applicable_rule(R,P,[Ag|SSx]).
	
@chk_sup1[atomic]
+!check_supported(R, P, SSr): not(supported(P,SS)) <-
	+supported(P,SSr).

@chk_sup2[atomic]
+!check_supported(R, P, SSr): 
		supported(P,SS) 
		& SS \== SSr 
		& pref(T) 
		& stronger(SSr,SS,T) <-
	//se jÃ¡ existe regra aplicÃ¡vel para P, decide pela mais forte
	-supported(P,SS);
	+supported(P,SSr).

	
/* O plano de aÃ§Ã£o a seguir Ã© disparado quando foi encontrada uma regra aplicÃ¡vel para P,
   ou se o corpo da regra jÃ¡ foi avaliado e nÃ£o for uma regrÃ¡ aplicÃ¡vel	 */
+waiting_for_support_return(CId,R,P,[],2): true <- //supportive_rule(R,A,P,_) <-
	.print("-- Encontrou regra aplicÃ¡vel (ou nÃ£o encontrou): " , R);
	-waiting_for_support_return(R,P,A,[],_);
	+support_finished_aux(P);
	for (waiting_for_support_return(S,P,Bs,1)) {
		.print("Existe processamento de suporte nÃ£o terminado: ", S);
		-support_finished_aux(P);		
	};
	?support_finished_aux(P);
	.print("Processamento de suporte terminado para ", P);
	+support_finished(CId,P);
	-support_finished_aux(P);	
	if (not(supported(P,_))) { // se descobriu-se que nÃ£o Ã© suportado, retorna
		!return_to_caller(CId,P);
	} else { // verifica tÃ©rmino de support negativo
		!check_negated_support_finished(CId,P);
	}.

/* Planos de aÃ§Ã£o que verificam tÃ©rmino do processamento do support para P */
	
+!check_negated_support_finished(CId,P): .negate(P,Q) & support_finished(CId,Q)  <-
	.print("Support terminado para ", P);
	!return_to_caller(CId,P).	

+!check_negated_support_finished(CId,P): .negate(P,Q) & not(support_finished(CId,Q))  <-
	.print("Support terminado para ", P);
	!support(CId, Q).

/* Planos de aÃ§Ã£o que retornam resultado da consulta: */

+!return_to_caller(CId,P): .negate(P,Q) & query_context(CId,A0,Q) <-
	!return_to_caller_final(CId,A0,Q).

+!return_to_caller(CId,P): query_context(CId,A0,P) <-
	!return_to_caller_final(CId,A0,P).	

+!return_to_caller_final(CId,A0,P): 
		.negate(P,Q)
		& supported(P,SS) 
		& (not(supported(Q,SSn)) | (supported(Q,SSn) & not(stronger(SSn, SS)))) <-
	!answer_provable(CId,P,SS,A0);
    !clear(CId, A0, P).
 
+!return_to_caller_final(CId,A0,P): 
		.negate(P,Q)
		& (not(supported(P,A,SS)) 
			| (
				supported(Q,A,SSn) 
				& 
				(
					not(supported(P,A,SS)) 
					| (supported(P,A,SS) & not(stronger(SS, SSn)))
				))) <-
    !answer_not_provable(CId,P,SS,A0);
    !clear(CId, A0, P).

+!answer_provable(CId,P,SS,A0): .my_name(Me) & Me == A0 <-
	+provable(P,SS)[source(Me), context(CId)].

+!answer_provable(CId,P,SS,A0): .my_name(Me) & Me \== A0 <-
	.send(A0, tell, provable(P,SS)[context(CId)]).
	
+!answer_not_provable(CId,P,SS,A0): .my_name(Me) & Me == A0 <-
	+~provable(P,SS)[source(Me), context(CId)].

+!answer_not_provable(CId,P,SS,A0): .my_name(Me) & Me \== A0 <-
	.send(A0, tell, ~provable(P,SS)[context(CId)]).

@clr
+!clear(CId, A0, P): true <-
	-query_context(CId,A0,P);
	-support_finished(CId,P);
	.negate(P,Q);
	-support_finished(CId,Q);
	if (not(query_context(CId,_,_))) {
		.abolish(rule(_,_,_,_)[context(CId)]);  //esquecimento
		.abolish(provable(P,_)[context(CId)]);
		.abolish(~provable(P,_)[context(CId)]);
		-focus_rules(CId,P);
	}.
	

/* Rules: */

known_agent(A) :- pref(T) & .member(A,T).

locally(CId,X) :- .print("r1") & rule(R,_,X,B)[rule_type(strict), context(CId)] & locally_provable(CId,B). //locally se Ã© strict e corpo Ã© locally_provable em A
locally(CId,X) :- .print("r2") & rule(R,_,X,B)[rule_type(strict), context(any)] & locally_provable(CId,B). //locally se Ã© strict e corpo Ã© locally_provable em A

locally_provable(CId,[]) :- .print("r3") & true.  //lista vazia sempre Ã© locally_provable (caso base)
locally_provable(CId,[X|B]) :- .print("r4") & locally(CId,X) & locally_provable(CId,B). //uma lista de literais Ã© locally_provable se cada item Ã© locally

stronger(A,B,T,B) :- .print("r5") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,A1).
stronger(A,B,T,A) :- .print("r6") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,B1).
weakest([X],X,_) :- true.
weakest([X|Tail],M,T) :- .print("r7") & weakest(Tail,M1,T) & weaker(X,M1,T,M).
weaker(Y1,Y2,T,Y1) :- .print("r8") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos1>Pos2.
weaker(Y1,Y2,T,Y2) :- .print("r9") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos2>Pos1.

