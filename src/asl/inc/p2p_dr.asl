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
		!p2p_dr(P,C,C)[for_literal(P)].

/* Planos de ação de consulta incluindo foco */
+!p2p_dr_with_focus_rules(P,C0,C,Rf,Z): true <-
		+focus_rules(P,C0,Rf);
		!p2p_dr(P,C0,C,Z).
		
+focus_rules(P,C,Rf) : true <-
		for (.member(L,Rf)) {
			if (not(strict_rule(_,_L,_)[focus_rule(P)])) {
				?rule_id(IDN);
				.concat("tr",IDN,ID);
				-+rule_id(IDN+1);
				+strict_rule(ID,C,L,[])[focus_rule(P)];		
			}
		}.		
		
/* Planos de ação: busca local	*/
+!p2p_dr(P,C0,C,Z): locally(P,_) <-
		 //se é provable pelas crenças locais (strict), acabou
		 .print("Achou locally ", P);
		+provable(P,C0,[C],Z).

+!p2p_dr(P,C0,C,Z): .negate(P,Q) & locally(Q,_) <-
		 //se é provable pelas crenças locais (strict), acabou
		 .print("Achou locally oposto ",P);
		+~provable(P,C0,[C],Z).		

/* Planos de ação: busca suporte */
+!p2p_dr(P,C0,C,Z): not(locally(P,_)) & support_finished(P) & .negate(P,Q) & support_finished(Q) <-
		+waiting_p2p_response(P,C0,Z);
		!return_to_caller(C,P).

+!p2p_dr(P,C0,C,Z): supported(P,C,_) <-
		+waiting_p2p_response(P,C0,Z);
		!return_to_caller(C,P).

+!p2p_dr(P,C0,C,Z): not(locally(P,_)) & not(support_finished(P)) <-
		+waiting_p2p_response(P,C0,Z);
		.print("Calling support for the literal. ",P);
		!support(P,C).

/* Planos de ação: suporte	*/		
+!support(P,C): supportive_rule(_,K,P,_) & (C==K | K==self) <-
		for (supportive_rule(R,K,P,_)){
             +waiting_for_support_return(R,P,C,[],0);
             .print("Calling support for rule - ",R);
             !support_aux(P,C,R);
        }.

-!support(P,C): true <-
		+support_finished(P);
		.print("Support failed for ", P);
		?rule_id(IDN);
		.concat("tr",IDN,ID);
		-+rule_id(IDN+1);
		+waiting_for_support_return(ID,P,C,[],2).  // ???
	
+!support_aux(P,C,R): supportive_rule(R,K,P,Body) & (C==K | K==self) <-
		.print("Trying support for rule ", R);
		if (.empty(Body)) {
			// se corpo da regra é vazio, então é uma regra aplicável (ver @apprule)
			?waiting_for_support_return(R,P,C,Current,_);
       		-+waiting_for_support_return(R,P,C,Current,1);
		} else {		
			for ( .member(B[source(K1)], Body) ){
				// adiciona cada membro do corpo ao quarto parâmetro de waiting_for_support_return
	             ?waiting_for_support_return(R,P,C,Current,_);	      
	            -+waiting_for_support_return(R,P,C,[B[source(K1)]|Current],1);
	        };   
	        ?waiting_for_support_return(R,P,C,Current,_);
	        for (.member(B[source(K2)], Body)){
	        	.print("Asking support for ",B[source(K2)]) 
	        	if (K2 == any) {
	        		!ask_all_known_contexts(P,C,B);
	        	} else {       
	        		if (K2 == C | K2 == self){
	        			!p2p_dr(B,C,C,P);  // consulta ao próprio contexto
	        		} else {
	        			!ask_other_agent(B,C,K2,P)
	        		};
	        	}
	        };            
        }.

/* Consulta aos contextos conhecidos */
+!ask_all_known_contexts(P,C,B): true <-
	for (known_context(K)) {
		if (not (K == C & P == B)) { // Risco de Loop???
			+waiting_for_support_from_arbitrary_context(B,K);
			if (K == C){
	        	!p2p_dr(B,C,C,P);
	        } else {
	        	!ask_other_context(B,C,K,P);
			};			
		};
	}.

+!ask_other_context(B,C,K,P): true <-
	if ((focus_rules(P,_,Rf) | (.negate(P,Q) & focus_rules(Q,_,Rf)))) {
		.send(K, achieve, p2p_dr_with_focus_rules(B,C,K,Rf,P));
	} else {
		.send(K, achieve, p2p_dr(B,C,K,P));
	}.


/* Planos de ação para tratamento de resposta às consultas */

/* Este plano é disparado quando chega uma resposta de consulta (provable para B) feita especificamente para K
   B é então removido da lista de termos do waiting_for_support_return  */
@pv1[atomic]
+provable(B,Q,SS,P)[source(K)]: context(C) & waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) & not(waiting_for_support_from_arbitrary_context(B,Q)) & (Q==K | K==self) <-
	.delete(B,Bs,NBs);
	-waiting_for_support_return(R,P,C,Bs,1);
	+waiting_for_support_return(R,P,C,NBs,1).


/* Este plano é disparado quando chega uma resposta de consulta (não provable para B) feita especificamente para K	
   A lista de termos do waiting_for_support_return é então esvaziada (pois se um termo não é provable, já invalida a regra) */
@pv2[atomic]
+~provable(B,Q,SS,P)[source(K)]: agent(C) & waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) & not(waiting_for_support_from_arbitrary_agent(B,Q)) & (Q==K | K==self) <-  
	-waiting_for_support_return(R,P,C,Bs,1);
	+waiting_for_support_return(R,P,C,[],2).


/* Os três planos a seguir tratam as respostas das concultas no caso de um termo ter sido 
   consultado a vários agentos (any)
   O raciocínio só segue quando todos os agentos responderem. */
@pv3[atomic]	
+~provable(B,Q,SS,P)[source(K)]: agent(C) & waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) & waiting_for_support_from_arbitrary_agent(B,Q) <-
	!evaluate_from_many_agents(B,Q).
	
@pv4[atomic]
+provable(B,Q,SS,P)[source(K)]: agent(C) & waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) & waiting_for_support_from_arbitrary_agent(B,Q) <-
	!evaluate_from_many_agents(B,Q).

@pvaux[atomic]
+!evaluate_from_many_agents(B,K) : waiting_for_support_return(R,P,C,Bs,1) & .member(B,Bs) <-
	-waiting_for_support_from_arbitrary_agent(B,K);
	if (not(waiting_for_support_from_arbitrary_agent(B,_))) { //Se todas as consultas sobre B já foram respondidas, então segue adiante 
		-waiting_for_support_return(R,P,C,Bs,1);
		if (not(provable(B,_,_,P))) { 
			+waiting_for_support_return(R,P,C,[],2);
		} else { 
			.delete(B,Bs,NBs);
			+waiting_for_support_return(R,P,C,NBs,1);
		};
		
	}.

/* O plano de ação a seguir é disparado quando todos os termos do corpo da regra R
   é avaliado e nenhum ~provable foi encontrado (flag 1)  */
@apprule
+waiting_for_support_return(R,P,C,[],1): supportive_rule(R,K,P,Body) & (C==K | K==self)   <-
	+applicable_rule(R,P,C,[]);
	.print("--- Regra aplicável encontrada para: ", P)
	.print("Regra: ", R)
	for (provable(B,Z,SSx,P) & .member(B,Body)) {
		?applicable_rule(R,P,C,SSr);
		.union([Z],SSr,X);
		.union(SSx,X,Y);
		-+applicable_rule(R,P,C,Y);
	};
	.print("Supportive set final da regra: ",SSr)
	?applicable_rule(R,P,C,SSr);
	if (not(supported(P,C,SS))) {	
		+supported(P,C,SSr);
	} else {
		//se já existe regra aplicável para P, decide pela mais forte
		?pref(C,T);
		if (supported(P,C,SS) & stronger(SSr,SS,T)) {
			-supported(P,C,SS);
			+supported(P,C,SSr);
		};
	};
	-waiting_for_support_return(R,P,C,[],1);
	+waiting_for_support_return(R,P,C,[],2).
	
/* O plano de ação a seguir é disparado quando foi encontrada uma regra aplicável para P,
   ou se o corpo da regra já foi avaliado e não for uma regrá aplicável	 */
+waiting_for_support_return(R,P,C,[],2): true <- //supportive_rule(R,C,P,_) <-
	.print("-- Encontrou regra aplicável (ou não encontrou): " , R);
	-waiting_for_support_return(R,P,C,[],_);
	+support_finished_aux(P);
	for (waiting_for_support_return(S,P,C,Bs,Status) & (Status < 2)) {
		.print("Existe processamento de suporte não terminado: ", S);
		-support_finished_aux(P);		
	};
	if (support_finished_aux(P)) {
		.print("Processamento de suporte terminado para ", P);
		+support_finished(P);
		-support_finished_aux(P);	
		if (not(supported(P,C,_))) { // se descobriu-se que não é suportado, retorna
			!return_to_caller(C,P);
		} else { // verifica término de support
			!check_support_finished(P,C);
		};		
	}.

/* Planos de ação que verificam término do processamento do support para P */
	
+!check_support_finished(P,C): .negate(P,Q) & (support_finished(P) & support_finished(Q))  <-
	.print("Support terminado para ", P);
	!return_to_caller(C,P).	

+!check_support_finished(P,C): .negate(P,Q) & support_finished(P) & not(support_finished(Q)) <-
	.print("Chamando suporte para negação de ",P);
	!support(Q,C).
	
//+!check_support_finished(P,C):  .negate(P,Q) & not(support_finished(P) & support_finished(Q)) <- true.
	

/* Planos de ação que retornam resultado da consulta: */

+!return_to_caller(C,P): .negate(P,Q) & waiting_p2p_response(Q,C0,Z) & not(waiting_p2p_response(P,C0,Z)) <-
	!return_to_caller_aux(C,Q,C0).

+!return_to_caller(C,P): waiting_p2p_response(P,C0,Z) <-
	!return_to_caller_aux(C,P,C0).	

+!return_to_caller_aux(C,P,C0): true <-
	?pref(C,T);
	?waiting_p2p_response(P,C0,Z);
	if (supported(P,C,SS)) {
		.negate(P,Q);
		if (supported(Q,C,SSn)) {
			if (not(stronger(SSn,SS,T))) {	
				.print("Suporte de P não é mais fraco que suporte de ~P. Respondendo provable: ", P);	
				!answer_provable(P,C,SS,Z,C0);					
			} else {	
				.print("Suporte de P é mais fraco que suporte de ~P. Respondendo não provable: ", P);
				!answer_not_provable(P,C,SSn,Z,C0);						
			};
		} else {	
			.print("~P não tem suporte. Respondendo provable: ", P);
			!answer_provable(P,C,SS,Z,C0);				
		};	
	} else {
		.print("P não é suportado. Respondendo não provable: ", P);
		!answer_not_provable(P,C,[],Z,C0);			
	};
	!clear(C,P,C0);
	-waiting_p2p_response(P,C0,Z).

+!answer_provable(P,C,SS,Z,C0): true <-
	if (C == C0) {
		+provable(P,C,SS,Z);
	} else {
		.send(C0, tell, provable(P,C,SS,Z));
	}.
	
+!answer_not_provable(P,C,SS,Z,C0): true <-
	if (C == C0) {
		+~provable(P,C,SS,Z);
	} else {
		.send(C0, tell, ~provable(P,C,SS,Z));
	}.

@clr
+!clear(C,P,C0) : true <-
	-waiting_p2p_response(P,C0);
	-support_finished(P);
	.negate(P,Q);
	-support_finished(Q);
	-focus_rules(P,C0,_);
	.abolish(strict_rule(_,_,_,_)[focus_rule(P)]);  //esquecimento
	.abolish(~provable(_,_,_,P));
	.abolish(~provable(_,_,_,P))
	.


/* Rules: */

known_agent(A) :- pref(C,T) & .member(A,T).
known_agent(A) :- agent(A).
strict_rule(Name,agent,Head[source(Agent)],[]) :- focus_rule(Name, Agent, Head).
//strict_rule(Name,Agent,Head[source(Agent)],[]) :- .print("Adding focus_rule locally") & focus_rules(Lit, Agent, Heads) & .member(Head,Heads).

supportive_rule(Name,Agent,Head,Body) :- .print("r3") & strict_rule(Name,Agent,Head,Body).
supportive_rule(Name,Agent,Head,Body) :- .print("r4") & defeasible_rule(Name,Agent,Head,Body).
supportive_rule(Name,Agent,Head,Body) :- .print("r5 ", Name) & mapping_rule(Name,Agent,Head,Body).
not_strict_supportive_rule(Name,Agent,Head,Body) :- .print("r6") & supportive_rule(Name,Agent,Head,Body) & not(strict_rule(Name,Agent,Head,Body)).

locally(X,C) :- .print("r7") & strict_rule(R,C,X,L) & locally_provable(L,C). //locally se é strict e corpo é locally_provable em C

locally_provable([],C) :- .print("r8") & true.  //lista vazia sempre é locally_provable (caso base)
locally_provable([X1|X2],C) :- .print("r9") & locally(X1,C) & locally_provable(X2,C). //uma lista de literais é locally_provable se cada item é locally

stronger(A,B,T,B) :- .print("r17") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,A1).
stronger(A,B,T,A) :- .print("r18") & weakest(A,A1,T) & weakest(B,B1,T) & weaker(A1,B1,T,B1).
weakest([X],X,_) :- true.
weakest([X|Tail],M,T) :- .print("r20") & weakest(Tail,M1,T) & weaker(X,M1,T,M).
weaker(Y1,Y2,T,Y1) :- .print("r21") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos1>Pos2.
weaker(Y1,Y2,T,Y2) :- .print("r22") & .nth(Pos1,T,Y1) & .nth(Pos2,T,Y2) & Pos2>Pos1.

