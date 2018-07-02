(*******************************************************************************
*
*	NAT
*
********************************************************************************
* Original : nat (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
*
* Theory of the natural numbers and addition function PLUS
*)

new_theory "nat";

new_type 0 "nat";


struct_axm (`:nat`,"strict",[("0",[]),("SUCC",[`n: nat`])]);

val zero_ty = `: 'zero_type`

val succ_ty = `:nat -> 'zero_type -> 'zero_type`;

new_constant ("NAT_REC",`: (^zero_ty * ^succ_ty) -> nat -> 'zero_type`);

(* this primitive recursion operator resembles that in Constructive
  Type Theory - it can express many nat functions *)
val NAT_REC =
   new_closed_axiom ("NAT_REC",
	`!nfun. !zerox : ^zero_ty. !succx: ^succ_ty.
	nfun == NAT_REC (zerox,succx) ==>
	nfun UU == UU /\
	nfun 0 == zerox /\
	(!n. ~n==UU ==>
	nfun (SUCC n) == succx n (nfun n))`);	

new_curried_infix ("+",`:nat -> nat -> nat`);

val PLUS =
   new_closed_axiom ("PLUS",
	`!m n. m + n == NAT_REC (n, \k. SUCC) m`);

timer true;

val NAT_REC_CLAUSES =
   save_thm ("NAT_REC_CLAUSES",
	GEN_ALL
	   (MATCH_MP NAT_REC
		(REFL `(NAT_REC (zerox,succx)) : nat -> ^zero_ty`)));

val NAT_TAC = STRUCT_TAC "nat" [];

val NAT_STRICT = axiom "nat" "STRICT";
val NAT_DEFINED = axiom "nat" "DEFINED";
val NAT_FLAT = theorem "nat" "FLAT";

(* functions defined by primitive recursion on total functions are total *)
val NAT_REC_TOTAL =
   prove_thm ("NAT_REC_TOTAL",
	`!zerox: ^zero_ty. ~ zerox == UU ==>
	!succx: ^succ_ty.
	   (!n nv. ~ n==UU ==> ~nv == UU ==> ~ succx n nv == UU) ==>
		!n. ~ n==UU ==> ~ NAT_REC (zerox,succx) n == UU`,
	 EVERY [NAT_TAC `n`,ASM_REWRITE_TAC [NAT_REC_CLAUSES]]);

val PLUS_TOTAL =
   prove_thm ("PLUS_TOTAL",
	`!m n. ~ m==UU ==> ~ n== UU ==> ~ m + n == UU`,
	REWRITE_TAC [NAT_REC_TOTAL,PLUS,NAT_DEFINED]) handle ? => EQ_REFL;

val PLUS_CLAUSES =
   prove_thm ("PLUS_CLAUSES",
	`!n. UU + n == UU /\
	 0 + n == n /\
	 (!m. ~ m==UU ==>
		(SUCC m) + n == SUCC (m + n))`,
	REWRITE_TAC [PLUS,NAT_REC_CLAUSES]);

val PLUS_ASSOC =
   prove_thm ("PLUS_ASSOC",
	`!m n k. ~ n==UU ==> (m + n) + k == m + (n + k)`,
	EVERY [NAT_TAC `m`,ASM_REWRITE_TAC [PLUS_CLAUSES,PLUS_TOTAL]]);

val PLUS_ZERO =
   prove_thm ("PLUS_ZERO",
	`!n. n + 0 == n`,
	EVERY [NAT_TAC `n`,ASM_REWRITE_TAC [PLUS_CLAUSES]]);

val PLUS_UU =
   prove_thm ("PLUS_UU",
	`!n. n + UU == UU`,
	EVERY [NAT_TAC `n`,ASM_REWRITE_TAC [PLUS_CLAUSES,NAT_STRICT]]);



val PLUS_SUCC =
   prove_thm ("PLUS_SUCC",
	`!m n. m + (SUCC n) == SUCC (m + n)`,
	EVERY [NAT_TAC `m`,ASM_REWRITE_TAC [PLUS_CLAUSES, NAT_STRICT]]);

val PLUS_COMM =
   prove_thm ("PLUS_COMM",
   	`!m n. m + n == n + m`,
EVERY [NAT_TAC `m`,ASM_REWRITE_TAC [PLUS_CLAUSES,PLUS_UU,PLUS_ZERO,PLUS_SUCC]]);

