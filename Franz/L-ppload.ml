(*****************************************************************************
*
*	PPLOAD
*
******************************************************************************
* Original: ppload (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Set PPLAMB axiom names
*)

val truth = `TRUTH()`;
val falsity = `FALSITY()`;

val TRUTH = axiom "PPLAMB" "TRUTH";

val LESS_REFL = axiom "PPLAMB" "LESS_REFL";

val LESS_ANTI_SYM = axiom "PPLAMB" "LESS_ANTI_SYM";

val LESS_TRANS = axiom  "PPLAMB" "LESS_TRANS";

val MONO = axiom "PPLAMB" "MONO";

val LESS_EXT = axiom "PPLAMB" "LESS_EXT";

val MINIMAL = axiom "PPLAMB" "MINIMAL";
	
val COND_CLAUSES = axiom "PPLAMB" "COND_CLAUSES";

val TR_CASES = axiom "PPLAMB" "TR_CASES";

val TR_LESS_DISTINCT = axiom "PPLAMB" "TR_LESS_DISTINCT";

val VOID_CASES = axiom "PPLAMB" "VOID_CASES";

val MK_PAIR = axiom "PPLAMB" "MK_PAIR";

val FST_PAIR = axiom "PPLAMB" "FST_PAIR";

val SND_PAIR = axiom "PPLAMB" "SND_PAIR";

val FIX_EQ = axiom "PPLAMB" "FIX_EQ";
