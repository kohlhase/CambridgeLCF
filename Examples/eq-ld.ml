(*eq-ld.ml  Commands for loading the theory eq*)

load_theory "eq";

val FLAT = axiom "eq" "FLAT";
val EQUAL_TT = axiom "eq" "EQUAL_TT";
val EQUAL_FF = axiom "eq" "EQUAL_FF";
val EQUAL_TOTAL = axiom "eq" "EQUAL_TOTAL";
val EQUAL_COMM = axiom "eq" "EQUAL_COMM";
val EQUAL_STRICT = axiom "eq" "EQUAL_STRICT";

val EQUAL_REFL = theorem "eq" "EQUAL_REFL";
val EQUAL_DIFF = theorem "eq" "EQUAL_DIFF";
val EQUAL_IFF_EQ = theorem "eq" "EQUAL_IFF_EQ";
val EQUAL_FF2 = theorem "eq" "EQUAL_FF2";
val EQUAL_COMM_IMP = theorem "eq" "EQUAL_COMM_IMP";
val EQUAL_CASES = theorem "eq" "EQUAL_CASES";
