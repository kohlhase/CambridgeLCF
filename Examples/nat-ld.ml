(*nat-ld.ml  Commands to load theory "nat"*)
load_theory "nat";
val NAT_STRICT = axiom "nat" "STRICT";
val NAT_DEFINED = axiom "nat" "DEFINED";
val NAT_FLAT = theorem "nat" "FLAT";

val NAT_REC_CLAUSES = theorem "nat" "NAT_REC_CLAUSES";
val NAT_REC_TOTAL = theorem "nat" "NAT_REC_TOTAL";
val PLUS_TOTAL = theorem "nat" "PLUS_TOTAL";
val PLUS_CLAUSES = theorem "nat" "PLUS_CLAUSES";
val PLUS_ASSOC = theorem "nat" "PLUS_ASSOC";
val PLUS_ZERO = theorem "nat" "PLUS_ZERO";
val PLUS_UU = theorem "nat" "PLUS_UU";
val PLUS_SUCC = theorem "nat" "PLUS_SUCC";
val PLUS_COMM = theorem "nat" "PLUS_COMM";
