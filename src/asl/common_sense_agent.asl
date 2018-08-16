// Agent hunterA in project mushroom_hunters


/* Initial beliefs and rules */


strict_rule(lcs1, self, amanita(M)[source(self)], [springtime_amanita(M)[source(self)]]).
//se houver mapping rule como common sense, pode dar loops e overheads
//mas por que eu precisaria de mapping rules no common sense?

//{ include("$jacamoJar/templates/common-moise.asl") }

// uncomment the include below to have an agent compliant with its organisation
//{ include("$moiseJar/asl/org-obedient.asl") }
