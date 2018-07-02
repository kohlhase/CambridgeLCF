(****************************************************************************
 *									    *
 *	ADMISS								    *
 *									    *
 ****************************************************************************
  Check admissability predicate;  all expressions should be true
  Converted to Standard ML by L C Paulson, March 1987
*)

new_theory "junk";

new_type 0 "nat";

val NAT_FLAT = ASSUME `!m n. m<<n  ==>  UU==m  \/  m==n : nat`;

val ty_thms = [NAT_FLAT, TR_CASES, VOID_CASES];

val ty_props = (mapfilter cfinite_type ty_thms, mapfilter finite_type ty_thms);

val (cfinite_types, finite_types) = ty_props ;

(*[false, true, true] *)
map (is_finite finite_types) [`:nat`, `:void`, `:tr`];

(*all true*)
map (is_cfinite ty_props) [`:nat`, `:void`, `:tr`];

val admits = admits_fm ty_props;

(*equiv and inequiv: all true*)
admits `f:nat->nat` (true,`fun f n <<UU : (nat -> nat)`);
admits `f:nat->nat` (true,`~ fun f n <<UU : (nat -> nat)`);
admits `f:nat->nat` (true,`~ fun f n ==UU : (nat -> nat)`);
admits `f:nat->nat` (true,`~ fun f n ==UU : nat`);
not (admits `f:nat->nat` (true,`~ f << fun f n : (nat -> nat)`));
not (admits `f:nat->nat` (true,`~ fun f n == f : (nat -> nat)`));


(*free chain-finite subterm*)
admits `f:nat->nat` (true,`?p:tr. fun f n == p`);
admits `f:nat->nat` (true,`!r:nat.?p:tr. fun f n == p`);

(*chain-finite subterms*)
(*leading universal quantifier*)
admits `f:nat->nat` (true, `!n:nat. ?p:tr. fun f n == p`);

(*finite quantification*)
admits `f:nat->nat` (true, `?p:tr. !n:nat. fun f n == p`);

(*leading existential quantifier*)
not (admits `f:nat->nat` (true, `?p: 'a. !n:nat. fun f n == p`));
not (admits `f:nat->nat` (true,`?n:nat. ?p:tr. fun f n == p`));


new_predicate ("PR", `: 'a`);

(*chain-finite subterm*)
admits `f:nat->nat` (true, `!n:nat. PR ((fun f n) : tr)`);
admits `f:nat->nat` (true, `!n:nat.?g:tr->nat. PR ((fun f n) : tr)`);
admits `f:nat->nat` (true, 
 `!k:nat. PR(k) ==> ?q:tr. PR(q) /\ !n:nat.?g:tr->nat. PR ((fun f n) : tr)`);

not (admits `f:nat->nat` (false, `!n:nat. PR ((fun f n) : tr)`));


(*free chain-finite term*)
admits_induction ty_thms `(fun f n <<UU /\ fun f n ==UU) ==> 
     !n:nat.?p:tr. PR ((fun f n) : tr)` `f:nat->nat`;

(*chain-finite term not free*)
not (admits_induction ty_thms `?n:nat. PR ((fun f n) : tr)` `f:nat->nat`);

(*positive equivalence, negative inequivalence*)
admits_induction ty_thms `!n:nat.?p:tr. f<<g /\ p==UU  ==>  f==UU` `f:nat->nat`;

(*negative free equivalence involving UU*)
admits_induction ty_thms 
	`!n':nat.?p:tr. f==UU  ==>  f<<g /\ h<<f` `f:nat->nat`;

(*negative free equivalence not involving UU*)
not (admits_induction ty_thms `!n':nat. f==f' ==>  p==TT` `f:nat->nat`);

(*negative (lhs) free inequivalence*)
admits_induction ty_thms `!n':nat. f<<UU ==> f==UU` `f:nat->nat`;
admits_induction ty_thms `f<<UU <=> f==UU` `f:nat->nat`;

(*negative (rhs) free inequivalence*)
not (admits_induction ty_thms `!n:nat. UU<<f  ==>  f==UU` `f:nat->nat`);

