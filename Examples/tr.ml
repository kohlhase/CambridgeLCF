(*tr.ML  Theory of truth-valued operators

AND and OR are sequential, not parallel like before -- they are not strict
in their second arguments.  The proofs of the simple lemmas, such as De
Morgan's theorem and the associative and distributive laws, are simple. With
parallel AND and OR, you often must argue by cases over all variables in the
assertion.  *)

new_theory "tr";



fun CASES_SIMP_TAC thl tm =
  EVERY [ REPEAT GEN_TAC,
          TR_CASES_TAC tm,
	  REWRITE_TAC thl ];

new_constant ("NOT", `:tr -> tr`);
new_curried_infix ("AND", `:tr -> tr -> tr`);
new_curried_infix ("OR",  `:tr -> tr -> tr`);


val NOT = 
new_closed_axiom ("NOT", `!p. NOT p == p => FF | TT`);

val OR =
new_closed_axiom ("OR",  `!p q. p OR q == p => TT | q`);

val AND =
new_closed_axiom ("AND", `!p q. p AND q == p => q | FF`);


(*Simplifying with these lemmas causes evaluation of expressions
involving AND, OR, and NOT, applied to constants.  There is no need to
rewrite AND, OR, and NOT to conditional expressions;  that would prevent
the use of their associative, distributive, and other properties.  *)

timer true;

val NOT_CLAUSES =
prove_thm ("NOT_CLAUSES", 
 `NOT UU == UU  /\  NOT TT == FF  /\  NOT FF == TT`,
 REWRITE_TAC [NOT, COND_CLAUSES]);


val OR_CLAUSES =
prove_thm ("OR_CLAUSES", 
 `!p. UU OR p == UU  /\  TT OR p == TT  /\  FF OR p == p`, 
 REWRITE_TAC [OR, COND_CLAUSES]);

val AND_CLAUSES =
prove_thm ("AND_CLAUSES", 
 `!p. UU AND p == UU  /\  TT AND p == p  /\  FF AND p == FF`, 
 REWRITE_TAC [AND, COND_CLAUSES]);



(************************************************************
 Algebraic Properties of AND, OR, NOT
 ************************************************************)


val NOT_NOT =
prove_thm ("NOT_NOT", `!p. NOT(NOT p) == p`, 
    CASES_SIMP_TAC [NOT_CLAUSES] `p`);


val AND_DEMORGAN =
prove_thm ("AND_DEMORGAN",
    `!p q. p AND q == NOT( (NOT p) OR (NOT q))`, 
    CASES_SIMP_TAC  [NOT_CLAUSES,  OR_CLAUSES,  AND_CLAUSES,  NOT_NOT] `p`);

val OR_DEMORGAN =
prove_thm ("OR_DEMORGAN", 
    `!p q. p OR q == NOT( (NOT p) AND (NOT q))`, 
    CASES_SIMP_TAC [NOT_CLAUSES,  OR_CLAUSES,  AND_CLAUSES,  NOT_NOT] `p`);


val OR_ASSOC =
prove_thm ("OR_ASSOC", `!p q r. p OR (q OR r) == (p OR q) OR r`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);

val AND_ASSOC =
prove_thm ("AND_ASSOC", `!p q r. p AND (q AND r) == (p AND q) AND r`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);

val AND_DIST =
prove_thm ("AND_DIST", `!p q r. p AND (q OR r) == (p AND q) OR (p AND r)`,
 CASES_SIMP_TAC [AND_CLAUSES, OR_CLAUSES] `p`);

val OR_DIST =
prove_thm ("OR_DIST", `!p q r. p OR (q AND r) == (p OR q) AND (p OR r)`,
 CASES_SIMP_TAC [AND_CLAUSES, OR_CLAUSES] `p`);

val AND_IDEM =
prove_thm ("AND_IDEM", `!p. p AND p == p`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);

val OR_IDEM =
prove_thm ("OR_IDEM", `!p. p OR p == p`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);


(************************************************************
 Totality of AND, OR, NOT
 ************************************************************)

val NOT_TOTAL =
prove_thm ("NOT_TOTAL", `!p. ~ p==UU  ==>   ~ NOT p == UU`,
 CASES_SIMP_TAC [NOT_CLAUSES] `p`);

val OR_TOTAL =
prove_thm ("OR_TOTAL",
 `!p q. ~ p==UU  ==>  ~ q==UU  ==>  ~ (p OR q) == UU`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);

val AND_TOTAL =
prove_thm ("AND_TOTAL",
 `!p q. ~ p==UU  ==>  ~ q==UU  ==>  ~ (p AND q) == UU`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);


val OR_R_TT =
prove_thm ("OR_R_TT",
 `!p. ~ p==UU  ==>  p OR TT == TT`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);


val OR_R_FF =
prove_thm ("OR_R_FF",
 `!p. p OR FF == p`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);


val AND_R_TT =
prove_thm ("AND_R_TT",
 `!p. p AND TT == p`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);


val AND_R_FF =
prove_thm ("AND_R_FF",
 `!p. ~ p==UU   ==>  p AND FF == FF`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);


val AND_R_FF2 =
prove_thm ("AND_R_FF2",
 `!p q. ~ p==UU  ==>  q==FF   ==>  p AND q == FF`,
 REPEAT STRIP_TAC  THEN  ASM_REWRITE_TAC [AND_R_FF]);


val AND_EQ_TT =
prove_thm ("AND_EQ_TT", `!p q. p AND q == TT  ==>  p==TT  /\  q==TT`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);


val AND_EQ_FF =
prove_thm ("AND_EQ_FF", `!p q. p AND q == FF  ==>  p==FF  \/  q==FF`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);

val AND_EQ_FF2 =
prove_thm ("AND_EQ_FF2", 
 `!p q. p AND q == FF  ==>  p==FF  \/  (p==TT  /\  q==FF)`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);


val OR_EQ_FF =
prove_thm ("OR_EQ_FF", `!p q. p OR q == FF  ==>  p==FF  /\  q==FF`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);

val OR_EQ_TT =
prove_thm ("OR_EQ_TT", `!p q. p OR q == TT  ==>  p==TT  \/  q==TT`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);

val OR_EQ_TT2 =
prove_thm ("OR_EQ_TT2", 
    `!p q. p OR q == TT  ==>  p==TT  \/  (p==FF  /\ q==TT)`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);

val NOT_EQ_TT =
prove_thm ("NOT_EQ_TT", `!p. NOT p == TT  ==>  ~ p==TT`,
 CASES_SIMP_TAC [NOT_CLAUSES] `p`);

val NOT_EQ_FF =
prove_thm ("NOT_EQ_FF", `!p. NOT p == FF  ==>  ~ p==FF`,
 CASES_SIMP_TAC [NOT_CLAUSES] `p`);

val NOT_EQ_TT_FF =
prove_thm ("NOT_EQ_TT_FF", `!p. NOT p == TT  ==>  p==FF`,
 CASES_SIMP_TAC [NOT_CLAUSES] `p`);

val NOT_EQ_FF_TT =
prove_thm ("NOT_EQ_FF_TT", `!p. NOT p == FF  ==>  p==TT`,
 CASES_SIMP_TAC [NOT_CLAUSES] `p`);




val AND_EQ_TT_IFF =
prove_thm ("AND_EQ_TT_IFF", 
 `!p q. p AND q == TT  <=>  p==TT  /\  q==TT`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);


val AND_EQ_FF_IFF =
prove_thm ("AND_EQ_FF_IFF",
 `!p q. ~ p==UU  ==>  (p AND q == FF  <=>  p==FF  \/  q==FF)`,
 CASES_SIMP_TAC [AND_CLAUSES] `p`);


val OR_EQ_FF_IFF =
prove_thm ("OR_EQ_FF_IFF",
 `!p q. p OR q == FF  <=>  p==FF  /\  q==FF`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);

val OR_EQ_TT_IFF =
prove_thm ("OR_EQ_TT_IFF",
 `!p q. ~ p==UU  ==>  (p OR q == TT  <=>  p==TT  \/  q==TT)`,
 CASES_SIMP_TAC [OR_CLAUSES] `p`);


val NOT_EQ_TT_IFF =
prove_thm ("NOT_EQ_TT_IFF",
 `!p. ~ p==UU  ==>  (NOT p == TT  <=>  ~ p==TT)`,
 CASES_SIMP_TAC [NOT_CLAUSES] `p`);

val NOT_EQ_FF_IFF =
prove_thm ("NOT_EQ_FF_IFF",
 `!p. ~ p==UU  ==>  (NOT p == FF  <=>  ~ p==FF)`,
 CASES_SIMP_TAC [NOT_CLAUSES] `p`);

val NOT_EQ_TT_FF_IFF =
prove_thm ("NOT_EQ_TT_FF_IFF",
 `!p. ~ p==UU  ==>  (NOT p == TT  <=>  p==FF)`,
 CASES_SIMP_TAC [NOT_CLAUSES] `p`);

val NOT_EQ_FF_TT_IFF =
prove_thm ("NOT_EQ_FF_TT_IFF",
 `!p. ~ p==UU  ==>  (NOT p == FF  <=>  p==TT)`,
 CASES_SIMP_TAC [NOT_CLAUSES] `p`);



val AND_COMM =
prove_thm ("AND_COMM",
   `!p q. ~ p==UU  ==>  ~ q==UU  ==>  p AND q == q AND p`,
   CASES_SIMP_TAC [] `p` THEN
   CASES_SIMP_TAC [AND_CLAUSES] `q`);

val OR_COMM =
prove_thm ("OR_COMM",
   `!p q. ~ p==UU  ==>  ~ q==UU  ==>  p OR q == q OR p`,
   CASES_SIMP_TAC [] `p` THEN
   CASES_SIMP_TAC [OR_CLAUSES] `q`);


val FLAT =
prove_thm ("FLAT",
 `!p:tr. !q:tr. p<<q  ==>  UU==p  \/  p==q`,
 CASES_SIMP_TAC [] `p`  THEN  CASES_SIMP_TAC [] `q`);

val COND_DEFINED =
prove_thm ("COND_DEFINED", 
    `!p x y. ~ p==UU  ==>  ~ x==UU  ==>  ~ y==UU  ==>  ~ (p=>x|y)==UU`,
    EVERY [
	CASES_SIMP_TAC [COND_CLAUSES] `p:tr`,
 	STRIP_TAC,
	RES_TAC]);

val COND_NOT =
prove_thm ("COND_NOT",
    `!p x y. NOT p => x|y == p => y|x`,
    CASES_SIMP_TAC [NOT_CLAUSES, COND_CLAUSES] `p`);

val FUN_COND =
prove_thm ("FUN_COND",
    `!f:'a->'b. f UU == UU  ==>  !p x y. f (p=>x|y) == p => f x | f y`,
    EVERY [
	REPEAT STRIP_TAC,
	COND_CASES_TAC,
	ASM_REWRITE_TAC [COND_CLAUSES]]);

val COND_COND_Y =
prove_thm ("COND_COND_Y",
    `!p x1 x2 y. (p => (p => x1|x2) | y) ==  (p=> x1|y):'a`,
    EVERY [
	REPEAT STRIP_TAC,
	COND_CASES_TAC,
	ASM_REWRITE_TAC [COND_CLAUSES]]);


val COND_X_COND =
prove_thm ("COND_X_COND",
    `!p x y1 y2. (p => x | (p => y1|y2)) ==  (p=>x|y2):'a`,
    EVERY [
	REPEAT STRIP_TAC,
	COND_CASES_TAC,
	ASM_REWRITE_TAC [COND_CLAUSES]]);


val COND_X_X =
prove_thm ("COND_X_X",
    `!p x. ~ p==UU  ==>  p=>x|x == x:'a`,
    EVERY [
	REPEAT GEN_TAC,
	COND_CASES_TAC,
	ASM_REWRITE_TAC [COND_CLAUSES]]);


val EQ_FF_IFF =
prove_thm ("EQ_FF_IFF",
    `!p. ~ p==UU  ==>  (p==FF  <=>  ~ p==TT)`,
    CASES_SIMP_TAC [] `p`);

val EQ_TT_IFF =
prove_thm ("EQ_TT_IFF",
    `!p. ~ p==UU  ==>  (p==TT  <=>  ~ p==FF)`,
    CASES_SIMP_TAC [] `p`);


val IFF_IFF_EQ =
prove_thm ("IFF_IFF_EQ",
   `!p q. ~ p==UU  ==>  ~ q==UU  ==>  ((p==TT <=> q==TT)  <=> p==q)`,
    CASES_SIMP_TAC [] `p` THEN    
    CASES_SIMP_TAC [] `q`);

close_theory();
