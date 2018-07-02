(***************************************************************************
 *									   *
 *		SEQ							   *
 *									   *
 ***************************************************************************
; Sample proofs involving sequences
  This session is described in Logic and Computation by Larry Paulson
*)

new_theory "sequences";

(*defining the type and operations*)

new_type 1 "seq";
struct_axm (`:'a seq`, "lazy",  [("SCONS",  [ `x: 'a`, `s: 'a seq` ])]);

new_constant("SEQ_WHEN", `:('a -> 'a seq -> 'b) -> ('a seq -> 'b)`);
new_constant("MAPS", `:('a -> 'b) -> ('a seq -> 'b seq)`);
new_paired_infix ("o", `: ('b->'c) * ('a->'b) -> ('a->'c)`);

val SEQ_WHEN_CLAUSES = new_closed_axiom ("SEQ_WHEN_CLAUSES", 
    `!h. SEQ_WHEN h UU == UU : 'b  /\
       (!x:'a. !s. SEQ_WHEN h (SCONS x s) == h x s)`);

val MAPS = new_closed_axiom ("MAPS",
    `!s. !f: 'a->'b. MAPS f s == SEQ_WHEN (\x t. SCONS (f x) (MAPS f t)) s`);

val COMPOSE = new_closed_axiom ("COMPOSE",
    `!f:'b->'c. !g: 'a->'b. f o g == \x.f(g x)`);



(*the proofs*)


val MAPS_UU = SPEC `UU:'a seq` MAPS;
val MAPS_SCONS = SPEC `SCONS x s` MAPS;
set_goal([], `!f: 'a->'b.  MAPS f UU == UU  /\
    (!x s. MAPS f(SCONS x s) == SCONS (f x) (MAPS f s))`);
expand (REWRITE_TAC [SEQ_WHEN_CLAUSES, MAPS_UU, MAPS_SCONS]);
val MAPS_CLAUSES = save_top_thm "MAPS_CLAUSES"; 



val SEQ_TAC = STRUCT_TAC "sequences" [];

set_goal([], 
  `!f:'b->'c. !g: 'a->'b. MAPS (f o g) == (MAPS f) o (MAPS g)`);
expand (REPEAT GEN_TAC);
expand (IMP_CHAIN_TAC EQ_EXT);
expand (SEQ_TAC `x: 'a seq`);
expand (REWRITE_TAC [MAPS_CLAUSES, COMPOSE]);
expand (ASM_REWRITE_TAC [MAPS_CLAUSES, COMPOSE]);
val MAPS_COMPOSE = save_top_thm "MAPS_COMPOSE"; 



(*descendant theory with proof by fixed point induction*)

new_theory "SEQ_OF";
new_parent "sequences";
val seq_of_ty = `:('a->'a) -> 'a -> 'a seq`;
new_constant("SEQ_OF_FUN", `:^seq_of_ty -> ^seq_of_ty`);
new_constant("SEQ_OF", `:^seq_of_ty`);

val SEQ_OF_FUN = new_closed_axiom ("SEQ_OF_FUN", 
    `SEQ_OF_FUN == \sf:^seq_of_ty. \f x. SCONS x (sf f (f x))`);

val SEQ_OF = new_closed_axiom ("SEQ_OF",
               `SEQ_OF : ^seq_of_ty == FIX SEQ_OF_FUN`);


set_goal([], `SEQ_OF == SEQ_OF_FUN SEQ_OF :^seq_of_ty`);
expand (REWRITE_TAC [SEQ_OF, FIX_EQ]);
val SEQ_OF_UNFOLD = save_top_thm "SEQ_OF_UNFOLD";


set_goal([], `!f. !x:'a. SEQ_OF f (f x) == MAPS f (SEQ_OF f x)`);
expand (SUBST_TAC [SEQ_OF]);
expand (INDUCT_TAC [] 
	[ (`SEQ_OF_FUN:^seq_of_ty -> ^seq_of_ty`, `sf:^seq_of_ty`) ]);
val MAPS_CLAUSES = theorem "sequences" "MAPS_CLAUSES"; 
expand (REWRITE_TAC [MAPS_CLAUSES, MIN_COMB]);
expand (REPEAT STRIP_TAC);
expand (ASM_REWRITE_TAC [SEQ_OF_FUN, MAPS_CLAUSES]);
val MAPS_SEQ_OF = save_top_thm "MAPS_SEQ_OF";




