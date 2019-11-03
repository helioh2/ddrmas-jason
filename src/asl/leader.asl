// leader agent

{ include("$jacamoJar/templates/common-cartago.asl") }
{ include("inc/p2p_dr.asl")}
{ include("common_sense_agent.asl") }
/* 
 * oi, meu nome é Helio Henrique. Digo que sou ante-paioso, mas poucos sabem que, na verdade, sou o maior paioso que já existiu
 * 
 * By Joao Leite, 
 * Based on implementation developed by Rafael Bordini, Jomi Hubner and Maicon Zatelli
 */

agent(leader).

max_catching(5).

collected(hunterA,0).
collected(hunterB,0).
collected(hunterC,0).
collected(hunterD,0).
collected(hunterE,0).

winning(none,0).

rule(ll1, leader, max_achieved(A), [achieved_max_collected(A)]) [rule_type(strict)].


achieved_max_collected(A) :- collected(A, X) & max_cathing(Y) & Y==X.

pref([hunterA, hunterE, hunterB, hunterC, hunterD]).
 

 

//the start goal only works after execise j)
//!start. 
//+!start <- tweet("a new mining is starting! (posted by jason agent)").

+catched[source(A)] : collected(A,S) & winning(L,SL) & S+1>SL
   <- 
   	-collected(A,S); 
      +collected(A,S+1); 
      -catched[source(A)]; 
      -+winning(A,S+1);
      .print("Agent ",A," is winning with ",S+1," pieces of gold");
      .broadcast(tell,winning(A,S+1)).

+catched[source(A)] : collected(A,S)
   <- -collected(A,S); 
      +collected(A,S+1);
      -catched[source(A)]; 
      .print("Agent ",A," has catched ",S+1," pieces of gold").
