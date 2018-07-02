(******************************************************************************
*
*	LIST
*
*******************************************************************************
* Original : list (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Theory of strict lists, with basic utilities.
*)

new_theory "list";

new_type 1 "list";

struct_axm (`: 'a list`, "strict",
	[("NIL",[]),("CONS",[`x: 'a`,`l: 'a list`])]);

val nil_ty = `:  'l`;
val cons_ty = `: 'a -> 'a list -> 'l -> 'l`;


new_constant ("LIST_REC",`: (^nil_ty * ^cons_ty) -> ( 'a list ) -> 'l`);

(* this prmitive recusrion operator resemblesthat n Constructive Type
   Theory - it can express many list functions easily *)
val LIST_REC =
   new_closed_axiom ("LIST_REC",
   	`!lfun. !nilx: ^nil_ty . !consx: ^cons_ty.
	lfun == LIST_REC (nilx,consx) ==>
	lfun UU == UU /\
	lfun NIL == nilx /\
	(!x l. ~x==UU ==> ~ l==UU ==>
	 lfun (CONS x l) == consx x l (lfun l))`);

new_curried_infix ("APP",`: 'a list -> 'a list -> 'a list`);

val APP =
   new_closed_axiom ("APP",
	`!l1 l2. l1 APP l2 == LIST_REC (l2,\x l.CONS x) l1 : 'a list`);

new_constant ("MAP",`: ( 'a -> 'b ) -> ( 'a list ) -> ( 'b list)`);

val MAP =
   new_closed_axiom
	("MAP",`!f: 'a -> 'b. MAP f == LIST_REC (NIL,\x l.CONS (f x))`);

new_constant ("FLATTEN",`: (( 'a list) list ) -> 'a list`);

val FLATTEN =
   new_closed_axiom ("FLATTEN",
	`FLATTEN== LIST_REC(NIL,\x l. op APP x) : (('a list)list) -> 'a list`);


val LIST_STRICT = axiom "list" "STRICT";
val LIST_DEFINED = axiom "list" "DEFINED";
val LIST_FLAT = theorem "list" "FLAT";


timer true;

val LIST_REC_CLAUSES =
  save_thm ("LIST_REC_CLAUSES",
	GEN_ALL
	   (MATCH_MP LIST_REC
		(REFL `LIST_REC(nilx,consx) : 'a list -> 'l`)));

val LIST_TAC = STRUCT_TAC "list" [];

(* functions defined by primitive recursion on total functions are total *)
val LIST_REC_TOTAL =
   prove_thm ("LIST_REC_TOTAL",
    `!nilx: ^nil_ty . ~ nilx == UU ==>
	!consx: ^cons_ty.
	(!x l lv. ~ x==UU ==> ~l==UU ==> ~lv==UU ==> ~consx x l lv == UU)
	==> !l. ~l==UU ==> ~LIST_REC (nilx,consx) l == UU`,
	EVERY [ LIST_TAC `l`,
	ASM_REWRITE_TAC [LIST_REC_CLAUSES]]);

val APP_TOTAL =
   prove_thm ("APP_TOTAL",
	`!l1 l2. ~ l1 == UU ==> ~l2 == UU ==> ~ l1 APP l2 == UU: 'a list`,
	REWRITE_TAC[ LIST_REC_TOTAL,APP,LIST_DEFINED]);

(* the definedness clauses in the CONS case are not necessary if you
  are willing to accept the Excluded Middle. x==UU \/ ~x==UU *)
val APP_CLAUSES =
   prove_thm ("APP_CLAUSES",
	`!l. UU APP l == UU /\
	NIL APP l == l /\
	(!x l2. ~ x==UU ==> ~l2==UU ==>
		(CONS x l2) APP l == CONS x (l2 APP l) : 'a list)`,
	REWRITE_TAC [APP,LIST_REC_CLAUSES]);

val APP_ASSOC =
   prove_thm ("APP_ASSOC",
	`!l1 l2 l3. ~ l2 == UU ==> ~ l3 == UU ==>
	l1 APP (l2 APP l3) == (l1 APP l2) APP l3 : 'a list`,
	EVERY [LIST_TAC `l1`,
	ASM_REWRITE_TAC [APP_CLAUSES,APP_TOTAL]]);

val APP_NIL =
   prove_thm ("APP_NIL",
	`!l. l APP NIL == l :  'a list`,
	EVERY [LIST_TAC `l`,ASM_REWRITE_TAC [APP_CLAUSES]]);

val APP_R_STRICT =
   prove_thm("APP_R_STRICT",
	`!l. l APP UU == UU : 'a list`,
	EVERY [LIST_TAC `l`,
	ASM_REWRITE_TAC [APP_CLAUSES,LIST_STRICT]]);

val MAP_TOTAL =
   prove_thm ("MAP_TOTAL",
	`!f: 'a -> 'b. (!x. ~ x==UU ==> ~ f x==UU) ==>
	!l. ~l==UU ==> ~ MAP f l == UU`,
	REWRITE_TAC [LIST_REC_TOTAL,MAP,LIST_DEFINED]);

val MAP_CLAUSES =
   prove_thm("MAP_CLAUSES",
	`!f : 'a -> 'b.
	MAP f UU == UU /\
	MAP f NIL == NIL /\
	(!x l. ~x==UU ==> ~l==UU ==>
	MAP f (CONS x l) == CONS (f x) (MAP f l))`,
	REWRITE_TAC [MAP,LIST_REC_CLAUSES]);

val MAP_APP =
   prove_thm("MAP_APP",
	`!f: 'a -> 'b.
	(!x. ~ x==UU ==> ~ f x == UU) ==>
	!l1 l2. ~ l2==UU ==> MAP f (l1 APP l2) == (MAP f l1) APP (MAP f l2)`,
	EVERY[LIST_TAC `l1`,
	ASM_REWRITE_TAC [MAP_CLAUSES,APP_CLAUSES,MAP_TOTAL,APP_TOTAL]]);

val MAP_MAP =
   prove_thm ("MAP_MAP",
	`!f: 'a -> 'b. !g: 'b -> 'c.
	(!x. ~x==UU ==> ~ f x==UU) ==>
	!l. MAP g (MAP f l) == MAP (\x: 'a.g(f x)) l`,
	EVERY [LIST_TAC `l`,
	ASM_REWRITE_TAC [MAP_CLAUSES,MAP_TOTAL]]);

val FLATTEN_TOTAL =
   prove_thm ("FLATTEN_TOTAL",
	`!l1. ~l1 ==UU ==> ~FLATTEN l1 == UU : ('a list) list`,
	REWRITE_TAC [LIST_REC_TOTAL,FLATTEN,LIST_DEFINED,APP_TOTAL]);

val FLATTEN_CLAUSES =
   prove_thm ("FLATTEN_CLAUSES",
	`FLATTEN UU == UU : 'a list /\
	FLATTEN NIL == NIL : 'a list /\
	!l: 'a list. !l1. ~ l==UU ==> ~l1==UU ==>
	FLATTEN (CONS l l1) == l APP (FLATTEN l1)`,
	REWRITE_TAC [LIST_REC_CLAUSES,FLATTEN]);



