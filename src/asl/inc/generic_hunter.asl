// miner agent

{ include("$jacamoJar/templates/common-cartago.asl")}
{ include("p2p_dr.asl")}


/* 
 * Based on implementation developed by Rafael Bordini, Jomi Hubner and Maicon Zatelli
 */

/* beliefs */
last_dir(null). // the last movement I did
free.
catched(0).

mapping_rule(self, can_collect(M, self)[source(self)], [~max_achieved(self)[source(leader)], edible(M)[source(any)] ]).


/* rules */
/* this agent program doesn't have any rules */


/* When free, agents wonder around. This is encoded with a plan that executes 
 * when agents become free (which happens initially because of the belief "free" 
 * above, but can also happen during the execution of the agent (as we will see below).
 *   
 * The plan simply gets two random numbers within the scope of the size of the grid 
 * (using an internal action jia.random), and then calls the subgoal go_near. Once the
 * agent is near the desired position, if free, it deletes and adds the atom free to 
 * its belief base, which will trigger the plan to go to a random location again.
 */

+free : gsize(_,W,H) & jia.random(RX,W-1) & jia.random(RY,H-1) 
   <-  .print("I am going to go near (",RX,",", RY,")");
       !go_near(RX,RY).
+free  // gsize is unknown yet
   <- .wait(100); -+free.
   
/* When the agent comes to believe it is near the location and it is still free, 
 * it updates the atom "free" so that it can trigger the plan to go to a random 
 * location again.
 */
+near(X,Y) : free <- -+free.



/* The following plans encode how an agent should go to near a location X,Y. 
 * Since the location might not be reachable, the plans succeed 
 * if the agent is near the location, given by the internal action jia.neighbour, 
 * or if the last action was skip, which happens when the destination is not 
 * reachable, given by the plan next_step as the result of the call to the 
 * internal action jia.get_direction.
 * These plans are only used when exploring the grid, since reaching the 
 * exact location is not really important.
 */

+!go_near(X,Y) : free
  <- -near(_,_); 
     -last_dir(_); 
     !near(X,Y).


// I am near to some location if I am near it 
+!near(X,Y) : (pos(AgX,AgY) & jia.neighbour(AgX,AgY,X,Y)) 
   <- .print("I am at ", "(",AgX,",", AgY,")", " which is near (",X,",", Y,")");
      +near(X,Y).
   
// I am near to some location if the last action was skip 
// (meaning that there are no paths to there)
+!near(X,Y) : pos(AgX,AgY) & last_dir(skip) 
   <- .print("I am at ", "(",AgX,",", AgY,")", " and I can't get to' (",X,",", Y,")");
      +near(X,Y).

+!near(X,Y) : not near(X,Y)
   <- !next_step(X,Y);
      !near(X,Y).
+!near(X,Y) : true 
   <- !near(X,Y).


/* These are the plans to have the agent execute one step in the direction of X,Y.
 * They are used by the plans go_near above and pos below. It uses the internal 
 * action jia.get_direction which encodes a search algorithm. 
 */

+!next_step(X,Y) : pos(AgX,AgY) // I already know my position
   <- jia.get_direction(AgX, AgY, X, Y, D);
      -+last_dir(D);
      D.
+!next_step(X,Y) : not pos(_,_) // I still do not know my position
   <- !next_step(X,Y).
-!next_step(X,Y) : true  // failure handling -> start again!
   <- -+last_dir(null);
      !next_step(X,Y).
  

/* The following plans encode how an agent should go to an exact position X,Y. 
 * Unlike the plans to go near a position, this one assumes that the 
 * position is reachable. If the position is not reachable, it will loop forever.
 */

+!pos(X,Y) : pos(X,Y) 
   <- .print("I've reached ",X,"x",Y).
+!pos(X,Y) : not pos(X,Y)
   <- !next_step(X,Y);
      !pos(X,Y).



/* Mushroom-searching Plans */

/* The following plan encodes how an agent should deal with a newly found piece 
 * of mushroom.
 * The first step changes the belief so that the agent no longer believes it is free. !!TIRAR
 * Then it adds the belief that there is mushroom in position X,Y, and 
 * prints a message. Finally, it calls a plan to handle that piece of mushroom.
 */

// perceived mushrooms are included as self beliefs (to not be removed once not seen anymore)
+cell(X,Y,mushroom) <- +mushroom(X,Y).

@pmushroom[atomic]           // atomic: so as not to handle another event until handle mushroom is initialised
+mushroom(X,Y) 
  :  not analysing_mushroom & free
  <- -free;
     .print("Mushroom perceived: ",mushroom(X,Y));
     !init_handle(mushroom(X,Y)).
 
     
/* The next plans encode how to handle a piece of mushroom.
 * The first one drops the desire to be near some location,  //TIRAR
 * which could be true if the agent was just randomly moving around looking for mushroom. //TIRAR
 * The second one simply calls the goal to handle the mushroom.
 * The third plan is the one that actually results in dealing with the mushroom. 
 * It raises the goal to go to position X,Y, then the goal to pickup the mushroom, 
 * then to go to the position of the depot, and then to drop the mushroom and remove 
 * the belief that there is mushroom in the original position. 
 * Finally, it prints a message and raises a goal to choose another mushroom piece.
 * The remaining two plans handle failure.
 */     

@pih1[atomic]
+!init_handle(Mushroom) 
  :  .desire(near(_,_)) 
  <- .print("Dropping near(_,_) desires and intentions to handle ",Mushroom);
     .drop_desire(near(_,_));
     !init_handle(Mushroom).
@pih2[atomic]
+!init_handle(Mushroom)
  :  pos(X,Y)
  <- .print("Going for ",Mushroom);
     !!handle(Mushroom). // must use !! to perform "handle" as not atomic

+!handle(mushroom(X,Y)) 
  :  not free 
  <- .print("Handling ",mushroom(X,Y)," now.");
     !pos(X,Y);
     !analyse(mushroom(X,Y));
     ?can_collect(mushroom(X,Y));
     !ensure(pick,mushroom(X,Y));
     .print("Finish handling ",mushroom(X,Y));
     ?catched(S);
     -+catched(S+1);
     .send(leader,tell,catched);
     !choose_mushroom.  //???

+!analyse(M) : true 
	<-  +analysing_mushroom;
		.print("Analysing mushrrom ",M);
		!p2p_dr(can_collect(M));
		-analysing_mushroom.




// if ensure(pick/drop) failed, pursue another mushroom
-!handle(G) : G
  <- .print("failed to catch mushroom ",G);
     .abolish(G); // ignore source
     !!choose_mushroom.
-!handle(G) : true
  <- .print("failed to handle ",G,", it isn't in the BB anyway");
     !!choose_mushroom.

/* The next plans deal with picking up and dropping mushroom. */

+!ensure(pick,_) : pos(X,Y) & mushroom(X,Y) & can_collect(mushroom(X,Y))
  <- 
  	 .print("Trying to pick ", mushroom(X,Y));
  	 pick; 
     -mushroom(X,Y). 
// fail if no mushroom there or not carrying_mushroom after pick! 
// handle(G) will "catch" this failure.




/* The next plans encode how the agent can choose the next mushroom piece 
 * to pursue (the closest one to its current position) or, 
 * if there is no known mushroom location, makes the agent believe it is free.
 */
+!choose_mushroom 
  :  not mushroom(_,_)
  <- -+free.

// Finished one mushroom, but others left
// find the closest mushroom among the known options, 
+!choose_mushroom 
  :  mushroom(_,_)
  <- .findall(mushroom(X,Y),mushroom(X,Y),LG);
     !calc_mushroom_distance(LG,LD);
     .length(LD,LLD); LLD > 0;
     .print("Mushroom distances: ",LD,LLD);
     .min(LD,d(_,NewG));
     .print("Next mushroom is ",NewG);
     !!handle(NewG).
-!choose_mushroom <- -+free.

+!calc_mushroom_distance([],[]).
+!calc_mushroom_distance([mushroom(GX,GY)|R],[d(D,mushroom(GX,GY))|RD]) 
  :  pos(IX,IY)
  <- jia.dist(IX,IY,GX,GY,D);
     !calc_mushroom_distance(R,RD).
+!calc_mushroom_distance([_|R],RD) 
  <- !calc_mushroom_distance(R,RD).


//+winning(A,S)[source(leader)] : .my_name(A)
//   <-  -winning(A,S); 
//       .print("I am the greatest!!!").
//
//+winning(A,S)[source(leader)] : true 
//   <-  -winning(A,S).




/* end of a simulation */

+end_of_simulation(S,_) : true 
  <- .drop_all_desires; 
     .abolish(mushroom(_,_));
     .abolish(picked(_));
     -+free;
     .print("-- END ",S," --").
     
     
     
     
     
     
     