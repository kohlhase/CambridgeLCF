(****************************************************************************
*
*	PPLAMB
*
*****************************************************************************
* Original: pplamb (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Set up theory PPLAMBDA
*)

new_theory "PPLAMB";
new_type 0 "void";
new_type 0 "tr";
new_type 2 "prod";
new_type 2 "fun";

new_constant ("()",` :void`);
new_constant ("TT",`:tr`);
new_constant ("FF",`:tr`);
new_constant ("UU",`: 'a`);
new_constant ("FIX", `: ( 'a -> 'a ) -> 'a`);
new_constant ("COND", `: tr -> 'a -> 'a  -> 'a`);
new_constant ("PAIR", `: 'a -> 'b -> ( 'a * 'b )`);
new_constant ("FST", `: 'a * 'b -> 'a`);
new_constant ("SND", `: 'a * 'b -> 'b`);

new_predicate ("equiv", `: 'a * 'a`);
new_predicate ("inequiv", `: 'a * 'a`);
new_predicate ("FALSITY", `:void`);
new_predicate ("TRUTH", `:void`);

val truth = `TRUTH()`;
val falsity = `FALSITY()`;

new_axiom("TRUTH",`TRUTH()`);
new_axiom("LESS_REFL", `!x: 'a . x<<x`);
new_axiom("LESS_ANTI_SYM" , `!x: 'a. !y: 'a. x<<y /\ y<<x ==> x==y`);
new_axiom ("LESS_TRANS", `!x: 'a. !y: 'a. !z: 'a. x<<y /\ y<<z ==> x<<z`);
new_axiom ("MONO", `!f: 'a -> 'b. !g: 'a -> 'b. !x y.
	      	f <<g /\ x<<y ==> f x << g y`);
new_axiom ("LESS_EXT", `!f: 'a -> 'b. !g: 'a -> 'b.
	 	(!x. f x << g x) ==> f <<g`);
new_axiom ("MINIMAL", `!x: 'a. UU<<x`);
new_axiom ("COND_CLAUSES", `!x y.
		UU => x | y == UU : 'a /\
		TT => x | y == x : 'a /\
		FF => x | y == y : 'a`);

(* A logical note: TR_CASES embeds classical reasoning into pplambda,
   since it allows you to reason by cases on wheather an arbitrary function 
   halts or not. As now  formulated, pplambda is not suitable for
   intuitionistic mathematics *)

new_axiom ("TR_CASES", `!p:tr. p==UU \/ p ==TT \/ p==FF`);
new_axiom ("TR_LESS_DISTINCT",
		`~ TT<<FF /\ ~ FF<<TT /\ ~ TT<<UU /\ ~ FF<<UU`);
new_axiom ("VOID_CASES", `!x:void. x==UU`);
new_axiom ("MK_PAIR", `!x: 'a * 'b. (FST x, SND x) ==x`);
new_axiom ("FST_PAIR" , `!x: 'a. !y: 'b. FST (x,y) == x`);
new_axiom ("SND_PAIR", `!x: 'a. !y: 'b. SND (x,y) ==y`);
new_axiom ("FIX_EQ", `!f: 'a -> 'a. f (FIX f) == FIX f`);

close_theory();
