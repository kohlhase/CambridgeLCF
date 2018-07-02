(*list-ld.ml  Commands to load theory "list"*)

load_theory "list";
val LIST_STRICT = axiom "list" "STRICT";
val LIST_DEFINED = axiom "list" "DEFINED";
val LIST_FLAT = theorem "list" "FLAT";
val LIST_REC_CLAUSES = theorem "list" "LIST_REC_CLAUSES";
val LIST_REC_TOTAL = theorem "list" "LIST_REC_TOTAL";
val APP_TOTAL = theorem "list" "APP_TOTAL";
val APP_CLAUSES = theorem "list" "APP_CLAUSES";
val APP_ASSOC = theorem "list" "APP_ASSOC";
val APP_NIL = theorem "list" "APP_NIL";
val APP_R_STRICT = theorem "list" "APP_R_STRICT";
val MAP_TOTAL = theorem "list" "MAP_TOTAL";
val MAP_CLAUSES = theorem "list" "MAP_CLAUSES";
val MAP_APP = theorem "list" "MAP_APP";
val MAP_MAP = theorem "list" "MAP_MAP";
val FLATTEN_TOTAL = theorem "list" "FLATTEN_TOTAL";
val FLATTEN_CLAUSES = theorem "list" "FLATTEN_CLAUSES";
