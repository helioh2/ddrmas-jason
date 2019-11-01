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
+!query_with_focus_rules(CId,P,Hist,Rf)[source(A0)]: true <-
	+focus_rules(CId,Rf);
	!query(CId,P,Hist)[source(A0)].

+focus_rules(CId,Rf) : true <-
	for (.member(R, Rf)) { +R; }.

/* Planos de aÃ§Ã£o: busca local	*/
+!query(CId,P,Hist)[source(A0)]: locally(CId,P) <-
	 //se Ã© provable pelas crenÃ§as locais (strict), acabou
	 .print("Achou locally ", P);
	 +query_context(CId,A0,P,Hist,[],[],false,false,false,false);		 
	 +answer(P,true,[])[context(CId)];
	 !return_to_caller(CId,P). 

+!query(CId,P,Hist)[source(A0)]: .negate(P,Q) & locally(CId,Q) <-
	 //se Ã© provable pelas crenÃ§as locais (strict), acabou
	 .print("Achou locally oposto ",Q);
	 +query_context(CId,A0,P,Hist,[],[],false,false);	//query_context(CId,A0,P,BS,SS,Unb,Sup)
	 +answer(P,false,[])[context(CId)];
	 !return_to_caller(CId,P).

/* Planos de aÃ§Ã£o: busca suporte */
+!query(CId,P,Hist)[source(A0)]: not(locally(CId,P)) & support_finished(CId,P) & .negate(P,Q) & support_finished(CId,Q) <-
	+query_context(CId,A0,P,Hist,[],[],false,false);
	!return_to_caller(A,P).

//+!query(CId,P,A0): supported(P,A,_) <-
//		+query_context(CId,A0);
//		+waiting_p2p_response(P,A0,Z); //???
//		!return_to_caller(A,P).

+!query(CId,P,Hist)[source(A0)]: not(locally(CId,P)) & not(support_finished(CId,P)) <-
		+query_context(CId,A0,P,Hist,[],[],false,false);
		.print("Calling support for the literal. ",P);
//		+waiting_support_for(CId, P);  //!!! DESENVOLVER FORMA DE EVITAR SUPPORTS ATROPELADOS PARA O MESMO CARA.
		!support(CId,P,Hist).
//		.negate(P,Q);
//		!support(CId,P);
//		!support(CId,Q).

/* Planos de aÃ§Ã£o: suporte	*/		
+!support(CId,P,Hist): rule(_,_,P,_)[context(C)] & (C == Cid | C == any) <-
	for (rule(R,_,P,Body)[context(C)] & (C == Cid | C == any)){
		+waiting_for_support_return(CId,R,P,Body,[],[],1);
	    for (.member(B[source(Ag)], Body)){
	    	!evaluate_body_member(CId,R,B,Ag,Hist);
	    };            
    }.

-!support(CId,P,Hist): true <-
	+support_finished(P);
	+answer(P,false,[])[context(CId)];
	.print("Support failed for ", P);
	!return_to_caller(CId, P).
	
+!evaluate_body_member(CId,R,B,Ag,Hist):
		Hist = hist(CId,P,L) & .member(B,L)
		& .my_name(Me) & Ag \== Me <-
	+cycle(CId,R,B);
	?waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1)
	.delete(B,Bs,NBs);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,[B|BSr],SSr,1).

+!evaluate_body_member(CId,R,B,Ag,Hist):
		Hist = hist(CId,P,L) & .member(B,L)
		& .my_name(Me) & Ag == Me & .length(L,T)<-
	+cycle(CId,R,B);
	for (.range(I, 0, T-1)) {
		if (.nth(I, L, B)) {
			.nth(I+1,L,D);
			?waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1)
			.delete(B,Bs,NBs);
			-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
			+waiting_for_support_return(CId,R,P,NBs,[D|BSr],SSr,1);	
		}		
	}.

+!evaluate_body_member(CId,R,B,Ag,Hist): 
		Hist = hist(CId,P,L) & not(.member(B,L)) 
		& Ag == any <-	
	!ask_all_known_agents(CId,B, hist(CId,B,[B|L])).
	
+!evaluate_body_member(CId,R,B,Ag,Hist): 
		Hist = hist(CId,P,L) & not(.member(B,L)) 
		& .my_name(Me) & (Ag == Me | Ag == self) <-
	!query(CId,B,hist(CId,B,[B|L]))[source(Me)].

+!evaluate_body_member(CId,R,B,Ag,Hist): 
		Hist = hist(CId,P,L) & not(.member(B,L)) 
		& .my_name(Me) & Ag \== any & Ag \== Me & Ag \== self  <-
	!ask_other_agent(CId,B,Ag,hist(CId,B,[B|L])).

/* Consulta aos agentos conhecidos */
+!ask_all_known_agents(CId,B): true <-
	.findall(Ag, known_agent(Ag), L);
	if (not(query_context(CId,_,B,_,_,_,_,_))) {
		.my_name(Me);
		.send(Me, achieve, query(CId,B));
		+waiting_for_support_from_arbitrary_agents(CId,B,[Me|L]);  //talvez otimizar usando somente contagem
	} else {
		+waiting_for_support_from_arbitrary_agents(CId,B,L); 
	}
    !ask_other_agent(CId,B,L).

+!ask_other_agent(CId,B,Ag, Hist): focus_rules(CId,Rf) <-
	.send(Ag, achieve, query_with_focus_rules(CId,B,Hist,Rf)).
		
+!ask_other_agent(CId,B,Ag, Hist): not(focus_rules(CId,Rf)) <-
	.send(Ag, achieve, query(CId,B,Hist)).


/* Planos de aÃ§Ã£o para tratamento de resposta Ã s consultas */

/* Este plano Ã© disparado quando chega uma resposta de consulta (provable para B) feita especificamente para K
   B Ã© entÃ£o removido da lista de termos do waiting_for_support_return  */
   
@pv11[atomic]
+answer(B,true,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B,LAg))
		& .my_name(Me) & Ag == Me  <-
	.delete(B,Bs,NBs);
	.union(BS,BSr,NBSr);
	.union(SS,SSr,NSSr);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,NBSr,NSSr,1);
	-answer(B,true,BS,SS)[source(Ag), context(CId)];
	+answer(B,true)[source(Ag), context(CId), chosen_to_support(P)].


@pv12[atomic]
+answer(B,true,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B,LAg) )
		& .my_name(Me) & Ag \== Me  <-
	.delete(B,Bs,NBs);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,[B|BSr],[B|SSr],1);
	-answer(B,true,BS,SS)[source(Ag), context(CId)];
	+answer(B,true)[source(Ag), context(CId), chosen_to_support(P)].	
	
	
/* Este plano Ã© disparado quando chega uma resposta de consulta (nÃ£o provable para B) feita especificamente para K	
   A lista de termos do waiting_for_support_return Ã© entÃ£o esvaziada (pois se um termo nÃ£o Ã© provable, jÃ¡ invalida a regra) */
@pv2[atomic]
+answer(B,false,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B,LAg)) <-  
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,[],[], [], 2);
	-answer(B,false,BS,SS)[source(Ag), context(CId)];
	+answer(B,false)[source(Ag), context(CId)].

	
@pv31[atomic]
+answer(B,undefined,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B,LAg) )
		& .my_name(Me) & Ag == Me  <-
	+cycle(CId,R,B);
	.delete(B,Bs,NBs);
	.union(BS,BSr,NBSr);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,NBSr,SSr,1);
	-answer(B,undefined,BS,SS)[source(Ag), context(CId)];
	+answer(B,undefined)[source(Ag), context(CId), chosen_to_support(P)].
	
@pv32[atomic]
+answer(B,undefined,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B,LAg))
		& .my_name(Me) & Ag \== Me   <-
	+cycle(CId,R,B);
	.delete(B,Bs,NBs);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,[B|BSr],SSr,1);
	-answer(B,undefined,BS,SS)[source(Ag), context(CId)];
	+answer(B,undefined)[source(Ag), context(CId), chosen_to_support(P)].
	

/* Os trÃªs planos a seguir tratam as respostas das concultas no caso de um termo ter sido 
   consultado a vÃ¡rios agentos (any)
   O raciocÃ­nio sÃ³ segue quando todos os agentos responderem. */

@pv4[atomic]
+answer(B,TV,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& waiting_for_support_from_arbitrary_agents(CId,R,B,LAg) <-
	if (Ag == self) {
		.my_name(Me);                                                         
		.delete(Me, LAg, NLAg);
	} else {
		.delete(Ag, LAg, NLAg);
	};
	-waiting_for_support_from_arbitrary_agents(CId,B,LAg);
	+waiting_for_support_from_arbitrary_agents(CId,B,NLAg);
	!evaluate_from_many_agents(CId,R,B). 
	
	
+!evaluate_from_many_agents(CId,R,B):
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& waiting_for_support_from_arbitrary_agents(CId,B,NL) & .empty(NL)
		& not(answer(B,true,_,_)[context(CId)])
		& not(answer(B,undefined,_,_)[context(CId)]) <-
	-waiting_for_support_from_arbitrary_agents(CId,B,NL); 
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,[],[], [], 2).
	
+!evaluate_from_many_agents(CId,R,B):
		waiting_for_support_from_arbitrary_agents(CId,B,NL)	& .empty(NL)
		& answer(B,true,_,_)[source(Ag), context(CId)] <-
	
	-waiting_for_support_from_arbitrary_agents(CId,B,NL);
	.findall(answer(B,true,BS,SS)[source(Ag), context(CId)], answer(B,true,BS,SS)[source(Ag), context(CId)], AnsTrue);
	!find_strongest(AnsTrue, answer(WB,true,WBS,WSS)[source(WAg), context(CId)]);		
	+answer(WB,true)[source(WAg), context(CId), chosen_to_support(P)];
	!evaluate_from_many_agents_finish(B).
	
+!evaluate_from_many_agents(CId,R,B):
		waiting_for_support_from_arbitrary_agents(CId,B,NL)	& .empty(NL)
		& answer(B,undefined,_,_)[source(Ag), context(CId)] <-
		
	-waiting_for_support_from_arbitrary_agents(CId,B,NL);
	.findall(answer(B,undefined,BS,SS)[source(Ag), context(CId)], answer(B,undefined,BS,SS)[source(Ag), context(CId)], AnsUndef);
	!find_strongest(AnsUndef, answer(WB,undefined,WBS,WSS)[source(WAg), context(CId)]);
	+answer(WB,undefined)[source(WAg), context(CId), chosen_to_support(P)];
	!evaluate_from_many_agents_finish(B).
	
+!evaluate_from_many_agents_finish(CId,R,B): .my_name(Me) & WAg \== Me <-
	-answer(B,_,_,_)[source(_), context(_)];   //Apaga todas as resposta !!!!
	.delete(B,Bs,NBs);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,[B|BSr],[B|SSr],1).
	
+!evaluate_from_many_agents_finish(CId,R,B): .my_name(Me) & WAg \== Me <-
	-answer(B,_,_,_)[source(_), context(CId)];   //Apaga todas as resposta !!!!
	.delete(B,Bs,NBs);
	.union(BS,BSr,NBSr);
	.union(SS,SSr,NSSr);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,NBSr,NSSr,1).

-!evaluate_from_many_agents(CId,R,B): true .

+!find_strongest(L,W): true <-
	+strongest_block_set(0);
	+strongest(0);
	for (.member(X,L) & X = answer(B,_,BS,SS)) { //!!!
		?strongest_block_set(BSw);
		?pref(T);
		if (BSw == 0 | stronger(BS, BSw, T)) {
			-+strongest_block_set(BS);
			-+strongest(X);
		}
	};
	?strongest(X);
	W = X.

/* O plano de aÃ§Ã£o a seguir Ã© disparado quando todos os termos do corpo da regra R
   Ã© avaliado e nenhum ~provable foi encontrado (flag 1)  */
@apprule
+waiting_for_support_return(CId,R,P,[],BS,SS,1): 
		rule(R,_,P,Body)[context(C)] & (C == Cid | C == any)
		& cycle(CId,R,_) <-
		
	+applicable_rule(R,P,[]);
	.print("--- Regra aplicÃ¡vel encontrada para: ", P);
	.print("Regra: ", R);
	for (answer(_,true)[source(_), context(CId), chosen_to_support(P)] & .member(B,Body)) {
		?applicable_rule(R,P,SSr);
		!update_applicable_rule(R,P,SSr,Ag,SSx);
	};
	?applicable_rule(R,P,SSr);
	.print("Supportive set final da regra: ",SSr);
	!check_supported(R,P,SSr);
	-waiting_for_support_return(R,P,A,[],1);
	+waiting_for_support_return(R,P,A,[],2).

@apprulecycle1
+waiting_for_support_return(CId,R,P,[],BSr,SSr,1): 
		rule(R,_,P,Body)[context(C)] & (C == Cid | C == any)
		& query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup)
		& (Unb == false | stronger(BSr, BSp)) <-
	-query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup);
	+query_context(CId,A0,P,Hist,BSr,SSp,true,Sup);
	+unblocked(CId,P,BSr);
	if (not(cycle(CId,R,_))) {
		if (Sup == false | stronger(SSr,SSp)) {
			?query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup);
			-query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup);
			+query_context(CId,A0,P,Hist,BSp,SSr,Unb,true);
			+supported(CId,P,SSr);
		}
	}
	-waiting_for_support_return(CId,R,P,[],BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,[],BSr,SSr,2).
	

	
/* O plano de aÃ§Ã£o a seguir Ã© disparado quando foi encontrada uma regra aplicÃ¡vel para P,
   ou se o corpo da regra jÃ¡ foi avaliado e nÃ£o for uma regrÃ¡ aplicÃ¡vel	 */
+waiting_for_support_return(CId,R,P,[],BSr,SSr,2): 
		query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup) <- //supportive_rule(R,A,P,_) <-
	.print("-- Encontrou regra aplicÃ¡vel (ou nÃ£o encontrou): " , R);
	-waiting_for_support_return(CId,R,P,[],BSr,SSr,2);
	if (not(waiting_for_support_return(CId,S,P,Bsx,BSx,SSx,1))) {
		.print("Processamento de suporte terminado para ", P);
		+support_finished(CId,P);
		if (Unb == false) { // se descobriu-se que nÃ£o Ã© suportado, retorna
			!return_to_caller(CId,P);
		} else { // verifica tÃ©rmino de support negativo
			!check_negated_support_finished(CId,P);
		}
	} else {
		.print("Existe processamento de suporte nÃ£o terminado: ", S);
	}.
	

/* Planos de aÃ§Ã£o que verificam tÃ©rmino do processamento do support para P */
	
+!check_negated_support_finished(CId,P): .negate(P,Q) & support_finished(CId,Q)  <-
	.print("Support terminado para ", P);
	!return_to_caller(CId,P).	

+!check_negated_support_finished(CId,P): 
		.negate(P,Q) 
		& not(support_finished(CId,Q))
		& query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup)  <-
	.print("Support terminado para ", P);
	.delete(P,Hist,HistNP);
	!support(CId, Q, [Q|HistNP]).

/* Planos de aÃ§Ã£o que retornam resultado da consulta: */

+!return_to_caller(CId,P): .negate(P,Q) & query_context(CId,A0,Q,_,_,_,_,_) <-
	!return_to_caller_final(CId,A0,Q).

+!return_to_caller(CId,P): query_context(CId,A0,P,_,_,_,_,_) <-
	!return_to_caller_final(CId,A0,P).	

+!return_to_caller_final(CId,A0,P): 
		query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup)
		& .negate(P,Q)
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
	-query_context(CId,A0,P,_,_,_,_,_);
	-support_finished(CId,P);
	.negate(P,Q);
	-support_finished(CId,Q);
	if (not(query_context(CId,_,_,_,_))) {
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

