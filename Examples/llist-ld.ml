(*llist-ld.ml  Commands to load the theory llist*)
val LAPP_CLAUSES = axiom "llist" "LAPP_CLAUSES";
val LMAP_CLAUSES = axiom "llist" "LMAP_CLAUSES";
val LAPP_ASSOC = theorem "llist" "LAPP_ASSOC";
val LMAP_LAPP = theorem "llist" "LMAP_LAPP";
val LMAP_LFLATTEN = theorem "llist" "LMAP_LFLATTEN";
