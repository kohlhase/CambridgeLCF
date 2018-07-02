(*LT-ld.ml  Commands to load the theory LT*)

load_theory "LT";
val LT = axiom "LT" "LT";
val LE = axiom "LT" "LE";
val NAT_FLAT_UU = theorem "LT" "NAT_FLAT_UU";
val LT_TOTAL = theorem "LT" "LT_TOTAL";
val LT_CLAUSES = theorem "LT" "LT_CLAUSES";
val LE_TOTAL = theorem "LT" "LE_TOTAL";
val LE_CLAUSES = theorem "LT" "LE_CLAUSES";
val LE_IFF = theorem "LT" "LE_IFF";
val LE_REFL = theorem "LT" "LE_REFL";
val LT_TRANS = theorem "LT" "LT_TRANS";
val LT_SUCC = theorem "LT" "LT_SUCC";
val SUCC_LT = theorem "LT" "SUCC_LT";
val LT_ANTI_REFL = theorem "LT" "LT_ANTI_REFL";
val LT_ANTI_SYM = theorem "LT" "LT_ANTI_SYM";
val ZERO_LE = theorem "LT" "ZERO_LE";
val LT_IMP_PLUS_LT = theorem "LT" "LT_IMP_PLUS_LT";
val LT_PLUS = theorem "LT" "LT_PLUS";
