rule_id(1).
context_id(1).
query_id(1).

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

+!query_original(P)[source(A0)]: not(.empty(Rf)) <-
	!new_query_context(CId);
	+original_query_context(CId);
	!pack_focus_rules(Rf);
	if (.empty(Rf)) {
		!query(CId,P,hist(CId, P, []))[source(A0)];
	} else {
		!query_with_focus_rules(CId,P,hist(CId, P, []),Rf)[source(A0)];
	}.

/* Planos de aÃƒÂ§ÃƒÂ£o de consulta incluindo foco */
+!query_with_focus_rules(CId,P,Hist,Rf)[source(A0)]: true <-
	if (not(focus_rules(CId,Rf))) {
		+focus_rules(CId,Rf);
	}
	
	!query(CId,P,Hist)[source(A0)].

+focus_rules(CId,Rf) : true <-
	for (.member(R, Rf)) { +R; }.

/* Planos de aÃƒÂ§ÃƒÂ£o: busca local	*/
+!query(CId,P,Hist)[source(A0)]: locally(CId,P) <-
	 //se ÃƒÂ© provable pelas crenÃƒÂ§as locais (strict), acabou
	 .print("Achou locally ", P);
	 +query_context(CId,A0,P,Hist); 
	 !return_to_caller(CId,P). 

+!query(CId,P,Hist)[source(A0)]: .negate(P,Q) & locally(CId,Q) <-
	 //se ÃƒÂ© provable pelas crenÃƒÂ§as locais (strict), acabou
	 .print("Achou locally oposto ",Q);
	 +query_context(CId,A0,P,Hist); 
	 !return_to_caller(CId,P).

/* Planos de aÃƒÂ§ÃƒÂ£o: busca suporte */
+!query(CId,P,Hist)[source(A0)]: not(locally(CId,P)) & support_finished(CId,P,_,_) & .negate(P,Q) & support_finished(CId,Q,_,_) <-
	+query_context(CId,A0,P,Hist); 
	!return_to_caller(A,P).

+!query(CId,P,Hist)[source(A0)]: not(locally(CId,P)) & support_finished(CId,P,_,_) & not(unblocked(CId,P,_)) & .negate(P,Q) & not(support_finished(CId,Q,_,_)) <-
	+query_context(CId,A0,P,Hist); 
	!return_to_caller(A,P).

+!query(CId,P,Hist)[source(A0)]: not(locally(CId,P)) & not(support_finished(CId,P,_,_)) <-
		+query_context(CId,A0,P,Hist); 
		.print("Calling support for the literal. ",P);
		!support(CId,P,Hist).

/* Planos de aÃƒÂ§ÃƒÂ£o: suporte	*/		
+!support(CId,P,Hist): rule(_,_,P,_)[context(C)] & (C == CId | C == any) <-
	for (rule(R,_,P,Body)[context(C)] & (C == CId | C == any)){
		+waiting_for_support_return(CId,R,P,Body,[],[],1);
	    for (.member(B[source(Ag)], Body)){
	    	!evaluate_body_member(CId,R,B,Ag,Hist);
	    };            
    }.

-!support(CId,P,Hist): true <-
	+support_finished(CId,P,[],[]);
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
	!ask_all_known_agents(CId,R,B,hist(CId,B,[B|L])).
	
+!evaluate_body_member(CId,R,B,Ag,Hist): 
		Hist = hist(CId,P,L) & not(.member(B,L)) 
		& .my_name(Me) & (Ag == Me | Ag == self) <-
	!query(CId,B,hist(CId,B,[B|L]))[source(Me)].

+!evaluate_body_member(CId,R,B,Ag,Hist): 
		Hist = hist(CId,P,L) & not(.member(B,L)) 
		& .my_name(Me) & Ag \== any & Ag \== Me & Ag \== self  <-
	!ask_other_agent(CId,B,Ag,hist(CId,B,[B|L])).

/* Consulta aos agentos conheCIdos */
+!ask_all_known_agents(CId,R,B,Hist): true <-
	.findall(Ag, known_agent(Ag), L);
	.my_name(Me);
	.send(Me, achieve, query(CId,B,Hist));
//	+waiting_for_support_from_arbitrary_agents(CId,R,B,[Me|L]);  //talvez otimizar usando somente contagem
    +waiting_for_support_from_arbitrary_agents(CId,R,B);
    !ask_other_agent(CId,B,L,Hist).

+!ask_other_agent(CId,B,Ag, Hist): focus_rules(CId,Rf) <-
	.send(Ag, achieve, query_with_focus_rules(CId,B,Hist,Rf)).
		
+!ask_other_agent(CId,B,Ag, Hist): not(focus_rules(CId,Rf)) <-
	.send(Ag, achieve, query(CId,B,Hist)).


/* Planos de aÃƒÂ§ÃƒÂ£o para tratamento de resposta ÃƒÂ s consultas */

/* Este plano ÃƒÂ© disparado quando chega uma resposta de consulta (provable para B) feita especificamente para K
   B ÃƒÂ© entÃƒÂ£o removido da lista de termos do waiting_for_support_return  */
   
@pv11[atomic]
+answer(B,true,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B))
		& .my_name(Me) & Ag == Me  <-
	.delete(B,Bs,NBs);
	.union(BS,BSr,NBSr);
	.union(SS,SSr,NSSr);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,NBSr,NSSr,1);
//	.count(answer(B,TV,BS,SS)[source(Ag), context(CId)], X);
//	.print("Numero de answers ", X)
	-answer(B,true,BS,SS)[source(Ag), context(CId)];
	+answer(B,true)[source(Ag), context(CId), chosen_to_support(P,R)].


@pv12[atomic]
+answer(B,true,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B) )
		& .my_name(Me) & Ag \== Me  <-
	.delete(B,Bs,NBs);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,[B|BSr],[B|SSr],1);
//	.count(answer(B,TV,BS,SS)[source(Ag), context(CId)], X);
//	.print("Numero de answers ", X)
	-answer(B,true,BS,SS)[source(Ag), context(CId)];
	+answer(B,true)[source(Ag), context(CId), chosen_to_support(P,R)].	
	
	
/* Este plano ÃƒÂ© disparado quando chega uma resposta de consulta (nÃƒÂ£o provable para B) feita especificamente para K	
   A lista de termos do waiting_for_support_return ÃƒÂ© entÃƒÂ£o esvaziada (pois se um termo nÃƒÂ£o ÃƒÂ© provable, jÃƒÂ¡ invalida a regra) */
@pv2[atomic]
+answer(B,false,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B)) <-  
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,[],[], [], 2);   // NAO PRECISA VER A RESPOSTA DOS DEMAIS MEMBROS DO CORPO. OS OUTROS QUE AINDA ENVIAREM RESPOSTAS, TAIS RESPOSTAS SERÃO DESCARTADAS !!!
//	.count(answer(B,TV,BS,SS)[source(Ag), context(CId)], X);
//	.print("Numero de answers ", X)
	-answer(B,false,BS,SS)[source(Ag), context(CId)];
	+answer(B,false)[source(Ag), context(CId)].

	
@pv31[atomic]
+answer(B,undefined,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B) )
		& .my_name(Me) & Ag == Me  <-
	+cycle(CId,R,B);
	.delete(B,Bs,NBs);
	.union(BS,BSr,NBSr);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,NBSr,SSr,1);
//	.count(answer(B,TV,BS,SS)[source(Ag), context(CId)], X);
//	.print("Numero de answers ", X)
	-answer(B,undefined,BS,SS)[source(Ag), context(CId)];
	+answer(B,undefined)[source(Ag), context(CId), chosen_to_support(P,R)].
	
@pv32[atomic]
+answer(B,undefined,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& not(waiting_for_support_from_arbitrary_agents(CId,R,B))
		& .my_name(Me) & Ag \== Me   <-
	+cycle(CId,R,B);
	.delete(B,Bs,NBs);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,[B|BSr],SSr,1);
//	.count(answer(B,TV,BS,SS)[source(Ag), context(CId)], X);
//	.print("Numero de answers ", X)
	-answer(B,undefined,BS,SS)[source(Ag), context(CId)];
	+answer(B,undefined)[source(Ag), context(CId), chosen_to_support(P,R)].
	

/* Os trÃƒÂªs planos a seguir tratam as respostas das concultas no caso de um termo ter sido 
   consultado a vÃƒÂ¡rios agentos (any)
   O raciocÃƒÂ­nio sÃƒÂ³ segue quando todos os agentos responderem. */

@pv4[atomic]
+answer(B,TV,BS,SS)[source(Ag), context(CId)]: 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
		& .member(B,Bs) 
		& waiting_for_support_from_arbitrary_agents(CId,R,B)
		& .count(answer(B,_,_,_)[context(CId)], X)
		& .count(known_agent(_), Y) & X == Y + 1 <-
//	if (Ag == self) {
//		.my_name(Me);                                                         
//		.delete(Me, LAg, NLAg);
//	} else {
//		.delete(Ag, LAg, NLAg);
//	};
	.print("Numero de answers ", X);
//	-waiting_for_support_from_arbitrary_agents(CId,R,B,LAg);
//	+waiting_for_support_from_arbitrary_agents(CId,R,B,NLAg);
	-waiting_for_support_from_arbitrary_agents(CId,R,B);
	!evaluate_from_many_agents(CId,R,B). 
//
//+answer(B,TV,BS,SS)[source(Ag), context(CId)]: true <-
//	.count(answer(B,TV,BS,SS)[source(Ag), context(CId)], X);
//	.print("Numero de answers ", X).


@ev1[atomic]
+!evaluate_from_many_agents(CId,R,B):
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1) 
//		& waiting_for_support_from_arbitrary_agents(CId,R,B,NL) & .empty(NL)  //LISTA NL VAZIA = TODOS OS AGENTES RESPONDERAM SOBRE B
		& not(answer(B,true,_,_)[context(CId)])     // SE NAO TIVER RESPOSTA TRUE NEM UNDEFINED
		& not(answer(B,undefined,_,_)[context(CId)]) <-
//	-waiting_for_support_from_arbitrary_agents(CId,R,B,NL); 
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,[],[], [], 2).
	
@ev2[atomic]
+!evaluate_from_many_agents(CId,R,B):
//		waiting_for_support_from_arbitrary_agents(CId,R,B,NL)	& .empty(NL)
		answer(B,true,_,_)[source(Ag), context(CId)] <-    // SE TIVER RESPOSTAS TRUE
	
//	-waiting_for_support_from_arbitrary_agents(CId,R,B,NL);
	.findall(answer(B,true,BS,SS)[source(Ag), context(CId)], answer(B,true,BS,SS)[source(Ag), context(CId)], AnsTrue);
	!find_strongest(AnsTrue, answer(WB,true,WBS,WSS)[source(WAg), context(CId)]);		
	+answer(WB,true)[source(WAg), context(CId), chosen_to_support(P,R)];
	!evaluate_from_many_agents_finish(CId,R,B,WAg).

@ev3[atomic]
+!evaluate_from_many_agents(CId,R,B):
//		waiting_for_support_from_arbitrary_agents(CId,R,B,NL)	& .empty(NL)
		not(answer(B,true,_,_)[source(Ag), context(CId)])   //SE TIVER RESPOSTAS UNDEFINED E NÃO TIVER RESPOSTAS TRUE
		& answer(B,undefined,_,_)[source(Ag), context(CId)] <-
		
	-waiting_for_support_from_arbitrary_agents(CId,R,B,NL);
	.findall(answer(B,undefined,BS,SS)[source(Ag), context(CId)], answer(B,undefined,BS,SS)[source(Ag), context(CId)], AnsUndef);
	!find_strongest(AnsUndef, answer(WB,undefined,WBS,WSS)[source(WAg), context(CId)]);
	+answer(WB,undefined)[source(WAg), context(CId), chosen_to_support(P,R)];
	!evaluate_from_many_agents_finish(B).

@ev4[atomic]
-!evaluate_from_many_agents(CId,R,B): true .
	
+!evaluate_from_many_agents_finish(CId,R,B,WAg): 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1)
		& .my_name(Me) & WAg \== Me <-
	-answer(B,_,_,_)[source(_), context(CId)];   //Apaga todas as resposta !!!!
	.delete(B,Bs,NBs);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,[B|BSr],[B|SSr],1).
	
+!evaluate_from_many_agents_finish(CId,R,B): 
		waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1)
		& .my_name(Me) & WAg == Me <-
	-answer(B,_,_,_)[source(_), context(CId)];   //Apaga todas as resposta !!!!
	.delete(B,Bs,NBs);
	.union(BS,BSr,NBSr);
	.union(SS,SSr,NSSr);
	-waiting_for_support_return(CId,R,P,Bs,BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,NBs,NBSr,NSSr,1).


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

/* O plano de aÃƒÂ§ÃƒÂ£o a seguir ÃƒÂ© disparado quando todos os termos do corpo da regra R
   ÃƒÂ© avaliado e nenhum ~provable foi encontrado (flag 1)  */

@apprulecycle1
+waiting_for_support_return(CId,R,P,[],BSr,SSr,1): 
		rule(R,_,P,Body)[context(C)] & (C == CId | C == any)
		//& query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup)
		& (not(unblocked(CId,P,BSp)) | stronger(BSr, BSp)) <-
	//-query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup);
	//+query_context(CId,A0,P,Hist,BSr,SSp,true,Sup);
	-unblocked(CId,P,_);
	+unblocked(CId,P,BSr);
	if (not(cycle(CId,R,_))) {
		if (not(supported(CId,P,SSp)) | stronger(SSr,SSp)) {
			//?query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup);
			//-query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup);
			//+query_context(CId,A0,P,Hist,BSp,SSr,Unb,true);
			-supported(CId,P,_);
			+supported(CId,P,SSr);
		}
	}
	-waiting_for_support_return(CId,R,P,[],BSr,SSr,1);
	+waiting_for_support_return(CId,R,P,[],BSr,SSr,2).
	

	
/* O plano de aÃƒÂ§ÃƒÂ£o a seguir ÃƒÂ© disparado quando foi encontrada uma regra aplicÃƒÂ¡vel para P,
   ou se o corpo da regra jÃƒÂ¡ foi avaliado e nÃƒÂ£o for uma regrÃƒÂ¡ aplicÃƒÂ¡vel	 */
+waiting_for_support_return(CId,R,P,[],BSr,SSr,2): true <-
		//query_context(CId,A0,P,Hist,BSp,SSp,Unb,Sup) <- //supportive_rule(R,A,P,_) <-
	.print("-- Encontrou regra aplicÃƒÂ¡vel (ou nÃƒÂ£o encontrou): " , R);
	-waiting_for_support_return(CId,R,P,[],BSr,SSr,2);
	if (not(waiting_for_support_return(CId,_,P,_,_,_,1))) {
		.print("Processamento de suporte terminado para ", P);
		if (supported(CId,P,SSp) & unblocked(CId,P,BSp)) {
			+support_finished(CId,P,BSp,SSp);
			!check_negated_support_finished(CId,P);
		}
		elif (not(supported(CId,P,_)) & unblocked(CId,P,BSp)) {
			+support_finished(CId,P,BSp,[]);
			!check_negated_support_finished(CId,P);
		}
		elif (not(unblocked(CId,P,_))) { // se descobriu-se que nÃƒÂ£o ÃƒÂ© suportado, retorna
			+support_finished(CId,P,[],[]);
			!return_to_caller(CId,P);
		};
	} else {
		.print("Existe processamento de suporte nÃƒÂ£o terminado: ", S);
	}.
	

/* Planos de aÃƒÂ§ÃƒÂ£o que verificam tÃƒÂ©rmino do processamento do support para P */
	
+!check_negated_support_finished(CId,P): .negate(P,Q) & support_finished(CId,Q,_,_)  <-
	.print("Support terminado para ", P);
	!return_to_caller(CId,P).	

+!check_negated_support_finished(CId,P): 
		.negate(P,Q) 
		& not(support_finished(CId,Q,_,_))
		& query_context(CId,_,P,hist(CId,P,LH))  <-
	.print("Support terminado para ", P);
	.delete(P,LH,NLH);
	!support(CId, Q, hist(CId,P,[Q|NLH])).

/* Planos de aÃƒÂ§ÃƒÂ£o que retornam resultado da consulta: */

+!return_to_caller(CId,P): .negate(P,Q) & query_context(CId,A0,Q,_) <-
	!return_to_caller_final(CId,A0,Q).

+!return_to_caller(CId,P): query_context(CId,A0,P,_) <-   //TO THINK: E SE EU TIVER CONSULTA PARA P E ~P NO MESMO CId E QUE NÃO SÃO OS SUPPORTS PARA OS OPOSTOS?? PENSAR EM EXEMPLO
                                                         // TALVEZ SEJA NECESSARIO QUE CADA CONSULTA NOVA, CRIE UM NOVO ID DE CONSULTA (DIFERENTE DO ID DE QUERY)
	!return_to_caller_final(CId,A0,P).	

+!return_to_caller_final(CId,A0,P): 
		query_context(CId,A0,P,Hist)
		& .negate(P,Q)
		& (locally(CId,P) |
			(	
				support_finished(CId,P,BSp,SSp)
				& support_finished(CId,Q,BSq,SSq)
				& supported(CId,P,SSp) 
				& (not(unblocked(CId,Q,BSq)) | stronger(SSp,BSq))
			)
		  ) <-
	!answer_true(CId,P,BSp,SSp,A0);
	!clear(CId, A0, P).
 
+!return_to_caller_final(CId,A0,P): 
		.negate(P,Q)
		& (locally(CId,Q) |
			(
				support_finished(CId,P,BSp,SSp)
				& not(unblocked(CId,P,SSp))
			)
			|
			(	
				support_finished(CId,P,BSp,SSp)
				& support_finished(CId,Q,BSq,SSq)
				& ( not(supported(CId,P,SSp))
					| (unblocked(CId,Q,BSq) & stronger(BSq,SSp)))
				& supported(CId,Q,SSq)
				& stronger(SSq,BSp)
			)
			
			
		  )
		<-
    !answer_false(CId,P,A0);
    !clear(CId, A0, P).
    
-!return_to_caller_final(CId,A0,P): 
		support_finished(CId,P,BSp,SSp)  <-
    !answer_undefined(CId,P,BSp,SSp,A0);
    !clear(CId, A0, P).

+!answer_true(CId,P,BS,SS,A0): .my_name(Me) & Me == A0 <-
	+answer(P,true,BS,SS)[source(Me), context(CId)].

+!answer_true(CId,P,BS,SS,A0): .my_name(Me) & Me \== A0 <-
	.send(A0, tell, answer(P,true,[],[])[context(CId)]).
	
+!answer_false(CId,P,A0): .my_name(Me) & Me == A0 <-
	+answer(P,false,[],[])[source(Me), context(CId)].

+!answer_false(CId,P,A0): .my_name(Me) & Me \== A0 <-
	.send(A0, tell, answer(P,false,[],[])[context(CId)]).
	
+!answer_undefined(CId,P,BS,SS,A0): .my_name(Me) & Me == A0 <-
	+answer(P,undefined,BS,SS)[source(Me), context(CId)].

+!answer_undefined(CId,P,BS,SS,A0): .my_name(Me) & Me \== A0 <-
	.send(A0, tell, answer(P,undefined,[],[])[context(CId)]).

@clr
+!clear(CId, A0, P): query_original(CId) <-
	!clear_final(CId);
	for (known_agent(A)) {
		.send(A, achieve, clear_final(CId));
	}.

-!clear(CId, A0, P): true.

+!clear_final(CId): true <-
	-query_context(CId,_,_,_);
	-query_context(CId,_,_,_);
	-support_finished(CId,_,_,_);
	.abolish(rule(_,_,_,_)[context(CId)]);  //esquecimento  !!!!s
	.abolish(answer(_,_,_,_)[context(CId)]); 
	-focus_rules(CId,_).
	
	

/* Rules: */

known_agent(A) :- pref(T) & .member(A,T).

locally(CId,X) :- .print("r1") & rule(R,_,X,B)[rule_type(strict), context(CId)] & locally_provable(CId,B). //locally se ÃƒÂ© strict e corpo ÃƒÂ© locally_provable em A
locally(CId,X) :- .print("r2") & rule(R,_,X,B)[rule_type(strict), context(any)] & locally_provable(CId,B). //locally se ÃƒÂ© strict e corpo ÃƒÂ© locally_provable em A

locally_provable(CId,[]) :- .print("r3") & true.  //lista vazia sempre ÃƒÂ© locally_provable (caso base)
locally_provable(CId,[X|B]) :- .print("r4") & locally(CId,X) & locally_provable(CId,B). //uma lista de literais ÃƒÂ© locally_provable se cada item ÃƒÂ© locally

stronger(A,B,T,B) :- .print("r5") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,A1).
stronger(A,B,T,A) :- .print("r6") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,B1).
weakest([X],X,_) :- true.
weakest([X|Tail],M,T) :- .print("r7") & weakest(Tail,M1,T) & weaker(X,M1,T,M).
weaker(Y1,Y2,T,Y1) :- .print("r8") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos1>Pos2.
weaker(Y1,Y2,T,Y2) :- .print("r9") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos2>Pos1.


