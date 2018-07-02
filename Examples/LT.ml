(*LT.ml
  The theory of the Less Than relation, LT, for the Natural Numbers.
  The proofs are analogous to those for the Occurrence relation, OCCS,
  which was defined on terms in the unification proof.
*)

new_theory "LT";

new_parent "nat";
new_parent "eq";
new_parent "tr";

new_curried_infix ("LE", `: nat -> nat -> tr`);
new_curried_infix ("LT", `: nat -> nat -> tr`);


(*Note use of "op" to suppress infix status of OR and LT*)
val LT = 
new_closed_axiom ("LT",
    `!m. op LT m == NAT_REC (FF, \n. op OR (m=n))`);


val LE =
new_closed_axiom ("LE", 
    `!m n. m LE n  ==  (m=n) OR (m LT n)`);

val FLAT = axiom "eq" "FLAT";
val REW_FLAT = REWRITE_RULE [REV_REWRITE FLAT];

val NAT_FLAT = theorem "nat" "FLAT";

val NAT_FLAT_UU = save_thm ("NAT_FLAT_UU", REW_FLAT NAT_FLAT);



use("nat-ld");
use("eq-ld");
use("tr-ld");


timer true;


val LT_TOTAL =
prove_thm ("LT_TOTAL",
    `!m n. ~ m==UU  ==>  ~ n==UU  ==>  ~ m LT n == UU`,
    REWRITE_TAC [NAT_REC_TOTAL, LT, EQUAL_TOTAL, OR_TOTAL, NAT_FLAT_UU]);



val LT_CLAUSES =
prove_thm ("LT_CLAUSES",
    `!m. m LT UU == UU  /\
	 m LT 0 == FF  /\
         (!n. ~ n==UU  ==>  m LT (SUCC n) == m LE n)`,
    REWRITE_TAC [LT, LE, NAT_REC_CLAUSES]);



val LE_TOTAL =
prove_thm ("LE_TOTAL",
    `!m n. ~ m==UU  ==>  ~ n==UU  ==>  ~ m LE n == UU`,
    REWRITE_TAC [LE, OR_TOTAL, EQUAL_TOTAL, NAT_FLAT_UU, LT_TOTAL]);


val LE_IFF =
prove_thm ("LE_IFF", 
    `!m n. ~ m==UU  ==>  ~ n==UU  ==>
    	(m LE n == TT  <=>  m==n  \/  m LT n ==TT)`,
  REWRITE_TAC [LE, OR_EQ_TT_IFF, EQUAL_IFF_EQ,  EQUAL_TOTAL, NAT_FLAT_UU]);


val LE_REFL = 
prove_thm ("LE_REFL",
   `!m. ~ m==UU  ==>  m LE m == TT`,
    REWRITE_TAC [LE_IFF]);


(*Expresses LE in terms of itself, rather than LT*)
val LE_CLAUSES = 
prove_thm ("LE_CLAUSES",
    `!m.   m LE UU == UU  /\
	   m LE 0 == (m=0)  /\
	 (!n. ~ n==UU  ==>
	   m LE (SUCC n) == (m=(SUCC n)) OR (m LE n))`,
  REWRITE_TAC [LE, LT_CLAUSES, OR_CLAUSES, OR_R_FF, EQUAL_STRICT]);






(***********************************************************)
(*     	          T R A N S I T I V I T Y		  *)
(***********************************************************)

val NAT_TAC = STRUCT_TAC "nat" [NAT_FLAT];


(*Note!  A slightly weaker theorem is useless for proving that LT is 
anti-symmetric and anti-reflexive:

    m LE n == TT  ==>  n LE k == TT   ==>  m LE k == TT
*)


val LT_TRANS =  
prove_thm ("LT_TRANS",
   `!m. ~ m==UU  ==>
    !n. ~ n==UU  ==> m LT n == TT  ==>
    !k. n LT k == TT  ==>  m LT k == TT`,
     EVERY [
	NAT_TAC `k`,
	ASM_REWRITE_TAC
	   [LT_CLAUSES, LE, OR_EQ_TT_IFF, EQUAL_IFF_EQ, NAT_FLAT_UU,
	    EQUAL_TOTAL],
	(* (a) only SUCC case remains *)
	DISCH_THEN (CUT_THM_TAC o REV_REWRITE) ,
	ASM_REWRITE_TAC []]);

(*case (a) the rewrite n==n' must be reoriented
`n == n'  ==>  m == n'  \/  m LT n' == TT`
    [ `~ m == UU` ]
    [ `~ n == UU` ]
    [ `m LT n == TT` ]
    [ `~ n' == UU` ]
    [ `n LT n' == TT  ==>  m LT n' == TT` ]
*)

    
    
(***********************************************************)
(*   	       I R R E F L E X I V I T Y		  *)
(***********************************************************)


(*The `step` property for LT -- used to prove irreflexivity.*)
val LT_SUCC =
prove_thm ("LT_SUCC",
    `!m. ~ m==UU  ==> m LT (SUCC m) == TT`,
    REWRITE_TAC 
       [LT_CLAUSES, LE, OR_EQ_TT_IFF,	
	EQUAL_REFL, EQUAL_TOTAL, NAT_FLAT_UU]);


(*Lemma for the anti-reflexivity proof 
|-`!n. ~ n == UU  ==>  (SUCC n) LT n == TT  ==>  n LT n == TT` *)
val SUCC_LT =
save_thm ("SUCC_LT",
    REWRITE_RULE [NAT_DEFINED, LT_SUCC] 
	(INST [ (`n`,`m`), (`SUCC n`, `n`), (`n`,`k`)] 
	   (hd (IMP_CANON LT_TRANS))));


val LT_ANTI_REFL =
prove_thm ("LT_ANTI_REFL",   `!m. ~ m LT m == TT`,
    EVERY [
	NAT_TAC `m`,    
	ASM_REWRITE_TAC
	   [LT_CLAUSES, LE, OR_EQ_TT_IFF, EQUAL_IFF_EQ,
	    EQUAL_TOTAL, NAT_DEFINED, NAT_FLAT_UU],
(*`~ SUCC n == n  /\  ~ (SUCC n) LT n == TT`
    [ `~ n == UU` ]  [ `~ n LT n == TT` ]  *)
	REPEAT STRIP_TAC,
	IMP_RES_THEN MP_TAC LT_SUCC,	(*works under assum. SUCC n==n *)
	IMP_RES_THEN MP_TAC SUCC_LT,	(*works under assum. SUCC n < n *)
	ASM_REWRITE_TAC []]);



val LT_ANTI_SYM =
prove_thm ("LT_ANTI_SYM",
    `!m n. ~ m==UU  ==>  ~ n==UU  ==>  ~ (m LT n == TT  /\  n LT m == TT)`,
    EVERY [
	REPEAT STRIP_TAC,
	IMP_RES_TAC LT_TRANS,
	IMP_RES_TAC LT_ANTI_REFL]);



val ZERO_LE =
prove_thm ("ZERO_LE",
    `!n. ~ n==UU  ==>  0 LE n == TT`,
    EVERY [
	NAT_TAC `n`,
	ASM_REWRITE_TAC
	   [LE_CLAUSES, OR_EQ_TT_IFF, EQUAL_IFF_EQ, 
	    NAT_DEFINED, EQUAL_TOTAL, NAT_FLAT_UU]]);



val LT_IMP_PLUS_LT =
prove_thm ("LT_IMP_PLUS_LT",
    `!k. ~ k==UU  ==>
     !m. ~ m==UU  ==>
     !n. m LT n == TT  ==>  (m + k) LT (n + k) == TT`,
    EVERY [
	NAT_TAC `n`,
	ASM_REWRITE_TAC
	   [LT_CLAUSES, LE, PLUS_CLAUSES, OR_EQ_TT_IFF, EQUAL_IFF_EQ,
	    EQUAL_TOTAL, PLUS_TOTAL, NAT_FLAT_UU]]);



val LT_PLUS =
prove_thm ("LT_PLUS",
    `!n. ~ n==UU  ==>  !m. ~ m==UU  ==>   n LE (m + n) == TT`,
    EVERY [
	NAT_TAC `m`,
	ASM_REWRITE_TAC
	   [LE_CLAUSES, LE_REFL, PLUS_CLAUSES, OR_EQ_TT_IFF, 
	    EQUAL_TOTAL, PLUS_TOTAL, NAT_DEFINED, NAT_FLAT_UU]]);

