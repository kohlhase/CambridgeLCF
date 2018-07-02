(***************************************************************************
 *									   *
 *	FIXED POINTS							   *
 *								     	   *
 * *************************************************************************
; Manna, Mathematical Theory of Computation, page 394
*)

new_theory "FUNCS";

new_constant ("P", `:'a->tr`);
new_constant ("G", `:'a->'a`);

new_constant ("H", `:'a->'a`);
new_constant ("K", `:('a->'a) -> ('a->'a)`);


val P_STRICT = new_closed_axiom ("P_STRICT", `P(UU:'a) == UU`);

val K = new_closed_axiom ("K", `K == \h x. P x => x | h(h(G x))`);

val H = new_closed_axiom ("H", `H == FIX K :'a->'a`);

(*
load_theory "FUNCS";
val P_STRICT = axiom "FUNCS" "P_STRICT";
val K = axiom "FUNCS" "K";
val H = axiom "FUNCS" "H";
val H_UNFOLD = theorem "FUNCS" "H_UNFOLD";
val H_STRICT = theorem "FUNCS" "H_STRICT";
val SUBST_OCCS_TAC = SUBS_OCCS_TAC;
*)


(*allows a single unfolding -- use with SUBST_TAC, not REWRITE_TAC! *)
set_goal([], `H == K H :'a->'a`);
expand (REWRITE_TAC [H, FIX_EQ]);
val H_UNFOLD = save_top_thm "H_UNFOLD";


set_goal([], `H UU == UU : 'a`);
expand (SUBST_TAC [H_UNFOLD]);
expand (REWRITE_TAC [K, P_STRICT, COND_CLAUSES]);
val H_STRICT = save_top_thm "H_STRICT";


set_goal([], `!x. H(H x) == H x`);
expand (SUBST_OCCS_TAC [ ([2,3], H) ]);
expand (INDUCT_TAC [] [ (`K: ('a->'a) -> ('a->'a)`, `h`) ]);
expand (REWRITE_TAC [H_STRICT, MIN_COMB]);
expand (REPEAT STRIP_TAC);
expand (REWRITE_TAC [K]);
expand (COND_CASES_TAC  THEN  ASM_REWRITE_TAC [H_STRICT]);
expand (SUBST_TAC [H_UNFOLD]);
expand (ASM_REWRITE_TAC [K, COND_CLAUSES]);
val H_IDEM = save_top_thm "H_IDEM";

(*

prove_thm("H_IDEM", `!x. H(H x) == H x`,
  EVERY [
    SUBST_OCCS_TAC [ ([2,3], H) ],
    INDUCT_TAC [] [ (`K: ('a->'a) -> ('a->'a)`, `h`) ],
    REWRITE_TAC [H_STRICT, MIN_COMB],
    REPEAT STRIP_TAC,
    REWRITE_TAC [K],
    COND_CASES_TAC  THEN  ASM_REWRITE_TAC [H_STRICT],
    SUBST_TAC [H_UNFOLD],
    ASM_REWRITE_TAC [K, COND_CLAUSES] ]);
*)
