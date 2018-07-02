(*seq-ld.ml  Commands to load theories "seq" and "SEQ_OF"*)

load_theory "sequences";
val SEQ_WHEN_CLAUSES = axiom "sequences" "SEQ_WHEN_CLAUSES";
val MAPS = axiom "sequences" "MAPS";
val COMPOSE = axiom "sequences" "COMPOSE";
val MAPS_CLAUSES = theorem "sequences" "MAPS_CLAUSES"; 
val MAPS_COMPOSE = theorem "sequences" "MAPS_COMPOSE"; 

load_theory "SEQ_OF";
val SEQ_OF_FUN = axiom "SEQ_OF" "SEQ_OF_FUN"; 
val SEQ_OF = axiom "SEQ_OF" "SEQ_OF";
val SEQ_OF_UNFOLD = theorem "SEQ_OF" "SEQ_OF_UNFOLD";
val MAPS_SEQ_OF = theorem "SEQ_OF" "MAPS_SEQ_OF";
