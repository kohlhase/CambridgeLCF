(****************************************************************************
 *									    *
 *	NAT2								    *
 *									    *
 ****************************************************************************
; Natural numbers using the Subgoal Package
 *)
lisp"(setq %margin 62)";
new_theory "nat";
new_type 0 "nat";
struct_axm (`:nat`, "strict",  
            [ ("0",     []),
              ("SUCC",  [ `n: nat` ])]);
new_constant("NAT_WHEN", `:'a -> (nat -> 'a) -> (nat -> 'a)`);
new_paired_infix ("+", `:nat*nat -> nat`);
val NAT_WHEN_CLAUSES = new_closed_axiom ("NAT_WHEN_CLAUSES", 
    `!x:'a. !f. NAT_WHEN x f UU == UU  /\
                NAT_WHEN x f 0 == x  /\
       (!m. ~ m==UU  ==>  NAT_WHEN x f (SUCC m) == f(m))`);
val PLUS = new_closed_axiom 
      ("PLUS", `!m n. m+n == NAT_WHEN n (\k.SUCC(k+n)) m`);

val PLUS_UU = SPEC `UU:nat` PLUS;
val PLUS_0 = SPEC `0` PLUS;
val PLUS_SUCC = SPEC `SUCC k` PLUS;
set_goal([], `!n.    UU + n == UU   /\   0 + n == n  /\
    (!m. ~ m==UU  ==>    (SUCC m) + n == SUCC (m + n))`);
expand (REWRITE_TAC [NAT_WHEN_CLAUSES,PLUS_UU,PLUS_0,PLUS_SUCC]);
val PLUS_CLAUSES = save_top_thm "PLUS_CLAUSES"; 

val NAT_TAC = STRUCT_TAC "nat" [];

set_goal([],   `!i j. ~ i==UU  ==>  ~ j == UU  ==>  ~ i + j == UU`);

expand (NAT_TAC `i`);
expand (REWRITE_TAC []);
expand (ASM_REWRITE_TAC [PLUS_CLAUSES]);
expand (ASM_REWRITE_TAC [PLUS_CLAUSES]);
val NAT_DEFINED = axiom "nat" "DEFINED";
val NAT_STRICT = axiom "nat" "STRICT";
expand (ASM_REWRITE_TAC [PLUS_CLAUSES, NAT_DEFINED]);
val PLUS_TOTAL = save_top_thm "PLUS_TOTAL";

    val PLUS_TOTAL = prove_thm ("PLUS_TOTAL1",
      `!i j. ~ i==UU  ==>  ~ j == UU  ==>  ~ i + j == UU`,
     NAT_TAC  `i`  THEN  ASM_REWRITE_TAC [PLUS_CLAUSES, NAT_DEFINED]);

set_goal([], `!i j k. ~ j==UU  ==>    (i + j) + k ==  i + (j + k)`);  
expand (NAT_TAC `i`  THEN  ASM_REWRITE_TAC [PLUS_CLAUSES]);
expand (ASM_REWRITE_TAC [PLUS_CLAUSES, PLUS_TOTAL]);
val PLUS_ASSOC = save_top_thm "PLUS_ASSOC";

    val PLUS_ASSOC = prove_thm ("PLUS_ASSOC1",
        `!i j k. ~ j==UU  ==>    (i + j) + k ==  i + (j + k)`,
     NAT_TAC  `i`  THEN  ASM_REWRITE_TAC [PLUS_CLAUSES, PLUS_TOTAL]);


set_goal([],   `!n. n + 0 == n`);
expand (NAT_TAC `n`  THEN  ASM_REWRITE_TAC [PLUS_CLAUSES]);
val PLUS_RIGHT_ZERO = save_top_thm "PLUS_RIGHT_ZERO";
set_goal([],   `!n. n + UU == UU`);
expand (NAT_TAC `n`  THEN  ASM_REWRITE_TAC [PLUS_CLAUSES,NAT_STRICT]);
val PLUS_RIGHT_UU = save_top_thm "PLUS_RIGHT_UU";
set_goal([],   `!i j. i + (SUCC j) == SUCC (i + j)`);
expand (NAT_TAC `i`  THEN  ASM_REWRITE_TAC [PLUS_CLAUSES]);
expand (REWRITE_TAC [NAT_STRICT]);
val PLUS_RIGHT_SUCC = save_top_thm "PLUS_RIGHT_SUCC";

set_goal([],   `!i j. i+j == j+i`);
expand (NAT_TAC `i`  THEN  
    REWRITE_TAC [PLUS_CLAUSES, PLUS_RIGHT_ZERO, PLUS_RIGHT_UU]);
expand (ASM_REWRITE_TAC [PLUS_CLAUSES, PLUS_RIGHT_SUCC]);
val PLUS_COMMUTE = save_top_thm "PLUS_COMMUTE";





new_theory "EQ";

new_parent "nat";
new_paired_infix ("=", `: nat*nat -> tr`);

val EQ = new_closed_axiom ("EQ", 
    `!m n. m=n == NAT_WHEN (NAT_WHEN TT (\j.FF) n)
                           (\i. NAT_WHEN FF (\j. i=j) n)
                           m`);


set_goal([],  `(!n. UU=n  == UU)  /\  (!m. m=UU == UU)  /\  0=0  == TT  /\
     (!n. ~ n==UU ==>  0=(SUCC n) == FF) /\
     (!m. ~ m==UU ==>  (SUCC m)=0 == FF) /\
     (!m n. ~ m==UU ==> ~ n==UU ==>  (SUCC m)=(SUCC n) == m=n)`);
val EQ_UU = SPEC `UU:nat` EQ;
val EQ_RIGHT_UU = SPECL [`m`, `UU:nat`] EQ;
val EQ_0 = SPEC `0` EQ;
val EQ_SUCC = SPEC `SUCC k` EQ;
expand (REWRITE_TAC [NAT_WHEN_CLAUSES, EQ_UU, EQ_RIGHT_UU,
                     EQ_0, EQ_SUCC]);
expand (NAT_TAC `m` THEN  ASM_REWRITE_TAC [NAT_WHEN_CLAUSES]);
val EQ_CLAUSES = save_top_thm "EQ_CLAUSES";
 



set_goal ([],  `!i j. ~ i==UU ==> ~ j==UU ==> (i=j == TT <=> i==j)`);
(*
expand (NAT_TAC `i`);
*)
val NAT_FLAT = theorem "nat" "FLAT";
val NAT_TAC = STRUCT_TAC "nat" [NAT_FLAT];
expand (NAT_TAC `i`);
expand (REWRITE_TAC []);
val EQ_IFF_ALL = theorem "nat" "EQ_IFF_ALL";
expand (NAT_TAC `j` THEN  ASM_REWRITE_TAC [EQ_CLAUSES, EQ_IFF_ALL]);
expand (NAT_TAC `j` THEN  ASM_REWRITE_TAC [EQ_CLAUSES, EQ_IFF_ALL]);
val EQUAL_IFF_EQ = save_top_thm "EQUAL_IFF_EQ";
