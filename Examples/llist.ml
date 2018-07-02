(*llist.ml
Theory of lazy lists, with basic utilities
	MAP
	APP  	(infixed append function)
	FLATTEN
*)



new_theory "llist";

new_type 1 "llist";

struct_axm  (`:'a llist`, "lazy",
     [("LNIL", []),  ("LCONS",  [`x:'a`, `ll:'a llist`]) ]);


new_curried_infix ("LAPP", `:'a llist -> 'a llist -> 'a llist`) ;


val LAPP_CLAUSES =  
new_closed_axiom ("LAPP_CLAUSES",
 `!ll. UU LAPP ll == UU  : 'a llist /\
       LNIL LAPP ll == ll  /\
       !x ll2. (LCONS x ll2) LAPP ll == LCONS x (ll2 LAPP ll)`);


new_constant ("LMAP", `: ('a -> 'b) -> ('a llist) -> ('b llist)`);

val LMAP_CLAUSES =
new_closed_axiom ("LMAP_CLAUSES",
    `!f : 'a -> 'b . 
       LMAP f UU == UU  /\
       LMAP f LNIL == LNIL /\
       (!x ll. LMAP f (LCONS x ll) == LCONS (f x) (LMAP f ll))`);


new_constant ("LFLATTEN", `:(('a llist)llist) -> 'a llist`);

val LFLATTEN_CLAUSES = 
new_closed_axiom ("LFLATTEN_CLAUSES",
    `LFLATTEN UU == UU : 'a llist  /\
     LFLATTEN LNIL == LNIL : 'a llist  /\
     !ll: 'a llist. !lll. LFLATTEN (LCONS ll lll) == ll LAPP (LFLATTEN lll)`);


timer true;


val LLIST_TAC = STRUCT_TAC "llist" [];




(*********************** A P P ************************)

 
val LAPP_ASSOC =
prove_thm ("LAPP_ASSOC",
  `!ll1 ll2 l3. ll1 LAPP (ll2 LAPP l3) ==  (ll1 LAPP ll2) LAPP l3 : 'a llist`,
  LLIST_TAC  `ll1`  THEN  ASM_REWRITE_TAC [LAPP_CLAUSES]);



val LAPP_LNIL = 
prove_thm("LAPP_LNIL", 
    `!ll. ll LAPP LNIL == ll : 'a llist`,
    LLIST_TAC `ll`  THEN  ASM_REWRITE_TAC [LAPP_CLAUSES]);

(*There is no theorem LAPP_R_STRICT for lazy lists!*)




(*********************** M A P ************************)



val LMAP_LAPP =
prove_thm ("LMAP_LAPP",
  `!f: 'a -> 'b. 
   !ll1 ll2. LMAP f (ll1 LAPP ll2) == (LMAP f ll1) LAPP (LMAP f ll2)`,
  LLIST_TAC `ll1`  THEN   ASM_REWRITE_TAC [LMAP_CLAUSES, LAPP_CLAUSES]);
    


val LMAP_LMAP =
prove_thm ("LMAP_LMAP",
 `!f : 'a -> 'b. !g: 'b -> 'c. 
    !ll. LMAP g (LMAP f ll) == LMAP (\x:'a.g(f x)) ll`,
  LLIST_TAC `ll`  THEN   ASM_REWRITE_TAC [LMAP_CLAUSES]);




(*********************** F L A T T E N ************************)


val LMAP_LFLATTEN =
prove_thm("LMAP_LFLATTEN", 
  `!f : 'a->'b. !lll. LFLATTEN (LMAP (LMAP f) lll) == LMAP f (LFLATTEN lll)`,
  LLIST_TAC `lll` THEN 
  ASM_REWRITE_TAC [LFLATTEN_CLAUSES, LMAP_CLAUSES, LMAP_LAPP]);

close_theory();
