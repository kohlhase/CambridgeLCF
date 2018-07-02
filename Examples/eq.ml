(********************************************************************************
*
*	EQ
*
*******************************************************************************
* Original : eq (Cambridge LCF)
* Converted to Standard ML by: P M Hedlund, Rutherford Appleton Lab. (1986)
*
* Theory for equality for flat domains.
*)

new_theory "eq";

new_curried_infix ("=", `: 'a -> 'a -> tr`);
new_predicate ("FLAT",`: 'a`);

val FLAT =
   new_closed_axiom ("FLAT",
	`FLAT(UU: 'a ) <=> (!x y. x<<y ==> UU==x \/ x==y : 'a )`);

val EQUAL_STRICT =
   new_closed_axiom ("EQUAL_STRICT", `!x: 'a. UU=x == UU /\ x=UU == UU`);


val EQUAL_COMM =
   new_closed_axiom("EQUAL_COMM",`!x: 'a . !y: 'a . x=y == y=x: 'a`);

(* loops if used as a conditional rewrite, since the antecedent mentions x *)
val EQUAL_TT =
   new_closed_axiom ("EQUAL_TT",`!x y. x=y == TT ==> x==y: 'a`);

val EQUAL_FF =
   new_closed_axiom ("EQUAL_FF",`!x y. x=y == FF ==> ~ x==y : 'a`);

val EQUAL_TOTAL =
   new_closed_axiom ("EQUAL_TOTAL",
   	`FLAT(UU: 'a ) ==>
		(!x: 'a. !y: 'a. ~ x == UU ==> ~ y == UU ==> ~ x=y == UU)`);


timer true;
val EQUAL_REFL =
   prove_thm ("EQUAL_REFL",
	`FLAT(UU: 'a ) ==> (!x: 'a. ~ x == UU ==> x=x == TT)`,
	EVERY [REPEAT STRIP_TAC,
		MP_TAC (SPEC `x=x` TR_CASES),
		ASM_REWRITE_TAC [EQUAL_TOTAL],
		DISCH_TAC,
		CUT_THM_TAC (REFL `x: 'a`),
		IMP_RES_TAC EQUAL_FF]);


val EQUAL_DIFF =
   prove_thm ("EQUAL_DIFF",
   `FLAT(UU: 'a ) ==> (!x y. ~ x==UU ==> ~ y==UU ==> ~ x==y ==> x=y == FF)`,
      EVERY [REPEAT STRIP_TAC,
      MP_TAC (SPEC `x=y` TR_CASES),
      ASM_REWRITE_TAC [EQUAL_TOTAL],
      DISCH_TAC,
      IMP_RES_TAC EQUAL_TT,
      RES_TAC]);

val EQUAL_IFF_EQ =
   prove_thm ("EQUAL_IFF_EQ",
	`FLAT(UU: 'a ) ==> !x: 'a. !y: 'a. ~ x==UU ==> ~ y==UU ==>
				(x=y == TT <=> x==y)`,
	EVERY[REPEAT (STRIP_TAC ORELSE IFF_TAC),
	IMP_RES_TAC EQUAL_TT,
	ASM_REWRITE_TAC [EQUAL_REFL]]);

(* used together with EQUAL_FF, you need not worry about the commutative law *)
val EQUAL_FF2 =
   prove_thm ("EQUAL_FF2",
	`!x y. x=y == FF ==> ~ y== x: 'a `,
	EVERY [ REPEAT GEN_TAC,
	SUBST_TAC [SPECL [`x: 'a `,`y: 'a `] EQUAL_COMM],
	MATCH_ACCEPT_TAC EQUAL_FF]);

(* for use with IMP_RES_TAC to flip the operands of = in assumptions *)
val EQUAL_COMM_IMP =
   prove_thm ("EQUAL_COMM_IMP",
	`!x: 'a. !y: 'a. !p. x=y == p ==> y=x == p`,
	EVERY [ REPEAT GEN_TAC,
	SUBST_TAC [SPECL [`x: 'a`,`y: 'a`] EQUAL_COMM],
	ASM_REWRITE_TAC []]);

val EQUAL_CASES =
   prove_thm ("EQUAL_CASES",
	`FLAT(UU: 'a ) ==> !x: 'a. !y: 'a. ~x==UU ==> ~y==UU ==>
				(x==y \/ ~x==y)`,
	EVERY [ REPEAT STRIP_TAC,
	MP_TAC (SPEC `x=y` TR_CASES),
	ASM_REWRITE_TAC [EQUAL_TOTAL],
	REPEAT STRIP_TAC,
	IMP_RES_TAC EQUAL_TT,
	IMP_RES_TAC EQUAL_FF,
	SELF_RES_TAC]);

