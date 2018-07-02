(*******************************************************************************
*
*	TAUT
*
********************************************************************************
* Original : taut (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Simplification of propositional tautologies
*)

(*	[A] B
	[B] A
   -----------------
      A <=> B
*)
fun FCONV_OF th1 th2 =
   CONJ_IFF (CONJ (DISCH (concl th2) th1)
		  (DISCH (concl th1) th2));

(*	TRUTH()   /\ A 		<=> A
	A         /\ TRUTH()	<=> A
	FALSITY() /\ A		<=> FALSITY()
	A	  /\ FALSITY()  <=> FALSITY()
*) 
fun TAUT_CONJ_FCONV w =
   let
	val (left,right) = dest_conj w 
   in
	if aconv_form left truth then
	   FCONV_OF (CONJUNCT2 (ASSUME w)) (CONJ TRUTH (ASSUME right))
	else if aconv_form right truth then
	   FCONV_OF (CONJUNCT1 (ASSUME w)) (CONJ (ASSUME left) TRUTH)
	else if aconv_form left falsity then
	   IFF_FALSITY (DISCH_ALL (CONJUNCT1 (ASSUME w)))
	else if aconv_form right falsity then
	    IFF_FALSITY (DISCH_ALL (CONJUNCT2 (ASSUME w)))
	else raise general with "TAUT_CONJ_FCONV"
   end handle 
	syntax => raise general with "TAUT_CONJ_FCONV" ||
	rule => raise general with "TAUT_CONJ_FCONV";


(* TRUTH()	\/ A	<=> TRUTH()
   A \/ FALSITY() \/ TRUTH() <=> TRUTH()
   FALSITY() 	\/ A	<=> A
   A 	\/  FALSITY() 
*)
fun TAUT_DISJ_FCONV w =
     let
	val (left,right) = dest_disj w 
   in
	if aconv_form left truth then
	   IFF_TRUTH (DISJ1 TRUTH right)
	else if aconv_form right truth then
	   IFF_TRUTH (DISJ2 left TRUTH)
	else if aconv_form left falsity then
	   FCONV_OF
		(DISJ_CASES (ASSUME w)
			    (CONTR right (ASSUME falsity))
			    (ASSUME right))
	   	(DISJ2 falsity (ASSUME right))
	else if aconv_form right falsity then
	   FCONV_OF
		(DISJ_CASES (ASSUME w)
		(ASSUME left)
		(CONTR left (ASSUME falsity)))
	        (DISJ1 (ASSUME left) falsity)
	else raise general with "TAUT_DISJ_FCONV"
    end handle 
	syntax => raise general with "TAUT_DISJ_FCONV" ||
	rule  => raise general with "TAUT_DISJ_FCONV";

(*	TRUTH()	==> A	<=> A
	A ==>	TRUTH()	<=> TRUTH()
	FALSITY() ==> A	<=> TRUTH()
	A ==> A		<=> TRUTH()
*)
fun TAUT_IMP_FCONV w =
   let
	val (left,right) = dest_imp w
   in
	if aconv_form left truth then
	   FCONV_OF (MP (ASSUME w) TRUTH) (DISCH truth (ASSUME right))
	else if aconv_form right truth then
	   IFF_TRUTH (DISCH left TRUTH)
	else if aconv_form left falsity then
	   IFF_TRUTH (DISCH_ALL (CONTR right (ASSUME falsity)))
	else if aconv_form left right then
	   IFF_TRUTH (DISCH_ALL (ASSUME left))
	else raise general with "TAUT_IMP_FCONV"
   end handle 
	syntax => raise general with "TAUT_IMP_FCONV"  ||
	rule  => raise general with "TAUT_IMP_FCONV";

(*	TRUTH() <=> A 	<=> A
	A <=> TRUTH()	<=> A
	FALSITY() <=> A	<=> ~A
	A <=> FALSITY()	<=> ~A
	A <=> A		<=> TRUTH()
*)
fun TAUT_IFF_FCONV w =
   let
	val (left,right) = dest_iff w
   in
	if aconv_form left truth then
	   FCONV_OF (MP (CONJUNCT1 (IFF_CONJ (ASSUME w))) TRUTH)
		(FSYM (IFF_TRUTH (ASSUME right)))
	else if aconv_form right truth then
	   FCONV_OF (MP (CONJUNCT2 (IFF_CONJ (ASSUME w))) TRUTH)
		(IFF_TRUTH (ASSUME left))
	else if aconv_form left falsity then
	   FCONV_OF (CONJUNCT2 (IFF_CONJ (ASSUME w)))
		(FSYM (IFF_FALSITY (ASSUME `~^right`)))
	else if aconv_form right falsity then
	   FCONV_OF (CONJUNCT1 (IFF_CONJ (ASSUME w)))
		(IFF_FALSITY (ASSUME `~^left`))
	else if aconv_form left right then
	   let
		val aimpa = DISCH_ALL (ASSUME left) 
	   in
		IFF_TRUTH (CONJ_IFF (CONJ aimpa aimpa))
	   end
	else raise general with "TAUT_IFF_FCONV"
   end handle 
	syntax => raise general with "TAUT_IFF_FCONV" ||
	rule => raise general with "TAUT_IFF_FCONV";

(* |-(!x.TRUTH()) <=> TRUTH() *)
val FORALL_TRUTH = save_thm ("FORALL_TRUTH",IFF_TRUTH (GEN `x: 'a` TRUTH));

(* |- (!x.FALSITY()) <=> FALSITY() *)
val FORALL_FALSITY =
   save_thm ("FORALL_FALSITY",IFF_FALSITY (DISCH_ALL (SPEC `x: 'a`
	(ASSUME `!x: 'a. FALSITY()`))));

(* |- (?x. TRUTH()) <=> TRUTH() *)
val EXISTS_TRUTH =
   save_thm ("EXISTS_TRUTH",IFF_TRUTH (EXISTS (`?x: 'a.TRUTH()`,`x: 'a`) TRUTH));

(* |- (?x. FALSITY()) <=> FALSITY() *)
val EXISTS_FALSITY = 
   save_thm ("EXISTS_FALSITY",
	IFF_FALSITY
	   (DISCH_ALL (CHOOSE (`x: 'a`,ASSUME `?x: 'a . FALSITY()`) (ASSUME falsity))));

val TAUT_FORALL_FCONV =
	FIRST_FCONV
	   [REWRITE_FCONV FORALL_TRUTH,REWRITE_FCONV FORALL_FALSITY];

val TAUT_EXISTS_FCONV =
   FIRST_FCONV
	[REWRITE_FCONV EXISTS_TRUTH,REWRITE_FCONV EXISTS_FALSITY];

val TRUTH_FCONV = (* Should be in fconv.ml *)
   REWRITE_FCONV o IFF_TRUTH o GSPEC;

(* handles distinctness of TT, FF, UU also reflextivity of << and == *)
val TAUT_PRED_FCONV =
   FIRST_FCONV
	((map FALSITY_FCONV
	   ((CONJUNCTS TR_EQ_DISTINCT) @ (CONJUNCTS TR_LESS_DISTINCT))) @
	 (map TRUTH_FCONV [EQ_REFL,LESS_REFL,MINIMAL]));

val BASIC_TAUT_FCONV =
   FIRST_FCONV
	[TAUT_CONJ_FCONV,TAUT_DISJ_FCONV,TAUT_IMP_FCONV,TAUT_IFF_FCONV,
	 TAUT_FORALL_FCONV,TAUT_EXISTS_FCONV,TAUT_PRED_FCONV];

(* (A\/B) ==> C <=> (A==>C) /\ (B==C) *)
fun DISJ_IMP_FCONV abimp =
   let
	val (ab,c) = dest_imp abimp 
	val (a,b) = dest_disj ab
	val abconj = mk_conj (mk_imp (a,c),mk_imp (b,c))
	val ABIMP = ASSUME abimp
	val (AIMP,BIMP) = CONJ_PAIR (ASSUME abconj)
   in
	FCONV_OF
	   (CONJ (DISCH a (MP ABIMP (DISJ1 (ASSUME a) b)))
		 (DISCH b (MP ABIMP (DISJ2 a (ASSUME b)))))
	   (DISCH ab (DISJ_CASES (ASSUME ab) (UNDISCH AIMP) (UNDISCH BIMP)))
   end handle 
	syntax => raise general with "DISJ_IMP_FCONV" ||
	rule => raise general with "DISJ_IMP_FCONV";

(* (A\/B) /\ C <=> (A/\C) \/ (B/\C), expands disjunctions to the right *)
fun DISJ_CONJ_FCONV abc_conj =
   let
	val (ab,c) = dest_conj abc_conj
	val (a,b) = dest_disj ab
	val ac_conj = mk_conj (a,c)
	val bc_conj = mk_conj (b,c)
   in
	FCONV_OF
	   (let
		val (AB,C) = CONJ_PAIR (ASSUME abc_conj)
	    in
		DISJ_CASES AB
		   (DISJ1 (CONJ (ASSUME a) C) bc_conj)
		   (DISJ2 ac_conj (CONJ (ASSUME b) C))
	    end)
	    (let
		val (A,C1) = CONJ_PAIR (ASSUME ac_conj)		
		val (B,C2) = CONJ_PAIR (ASSUME bc_conj)
	    in
		DISJ_CASES (ASSUME (mk_disj (ac_conj,bc_conj)))
		   (CONJ (DISJ1 A b) C1)
		   (CONJ (DISJ2 a B) C2)
	    end)
   end handle 
	syntax => raise general with "DISJ_CONJ_FCONV" ||
	rule => raise general with "DISJ_CONJ_FCONV";

(* C /\ (A\/B) <=> (C/\A) \/ (C/\), expands disjunctions to the left *)
fun CONJ_DISJ_FCONV cab_conj =
   let
	val (c,ab) = dest_conj cab_conj
	val (a,b) = dest_disj ab
	val ca_conj = mk_conj (c,a)
	val cb_conj = mk_conj (c,b)
   in
	FCONV_OF
	   (let
		val (C,AB) = CONJ_PAIR (ASSUME cab_conj)
	    in
		DISJ_CASES AB
		   (DISJ1 (CONJ C (ASSUME a)) cb_conj)
		   (DISJ2 ca_conj (CONJ C (ASSUME b)))
	    end)
	   (let
		val (C1,A) =CONJ_PAIR (ASSUME ca_conj)	
		val (C2,B) = CONJ_PAIR (ASSUME cb_conj)
	    in
		DISJ_CASES (ASSUME (mk_disj (ca_conj,cb_conj)))
		   (CONJ C1 (DISJ1 A b))
		   (CONJ C2 (DISJ2 a B))
	    end)
   end handle 
	syntax => raise general with "CONJ_DISJ_FCONV" ||
	rule => raise general with "CONJ_DISJ_FCONV";

(* (?.xA(x)) ==> B <=> !x'.(A(x') ==> B), expands negated existentials *)
fun EXISTS_IMP_FCONV xaimp =
   let
	val (xa,b) = dest_imp xaimp
	val (x,a) =dest_exists xa
	val x' = variant (form_frees b) x 
	val a' = subst_form [(x',x)] a
	val faimp = mk_forall (x',mk_imp (a',b))
   in
	FCONV_OF
		(((GEN x') o (DISCH a') o (MP (ASSUME xaimp)) o
		  (EXISTS (xa,x')) o ASSUME) a')
		(((DISCH xa) o (CHOOSE (x',ASSUME xa)) o
		  UNDISCH o (SPEC x')) (ASSUME faimp))
   end handle 
	syntax => raise general with "EXISTS_IMP_FCONV" ||
	rule => raise general with "EXISTS_IMP_FCONV";

(* (?x.A(x)) /\ B <=>  ?x'.(A(x) /\ B), expands existentials to the right *)
fun EXISTS_CONJ_FCONV xa_conj =
   let
	val (xa,b) = dest_conj xa_conj
	val (x,a) = dest_exists xa 
	val x' = variant (form_frees b) x
	val a' = subst_form [(x',x)] a
	val xa'_conj = mk_exists (x',mk_conj (a',b))
   in
	FCONV_OF
	   (let
		val (XA,B) = CONJ_PAIR (ASSUME xa_conj)
	    in
		CHOOSE (x', XA) (EXISTS (xa'_conj ,x') (CONJ (ASSUME a') B))
	    end)	
	   (let
	   	val (A',B) = CONJ_PAIR (ASSUME (mk_conj (a',b)))
	    in
		CHOOSE (x',ASSUME xa'_conj) (CONJ (EXISTS (xa,x') A') B)
	    end)	
   end handle 
	syntax => raise general with "EXISTS_CONJ_FCONV" ||
	rule => raise general with "EXISTS_CONJ_FCONV";

(* B /\ (?x.A(x)) <=> ?x'.(B/\A(x)), exp. existentials to the right *)
fun CONJ_EXISTS_FCONV xa_conj = 
   let
	val (b,xa) = dest_conj xa_conj
	val (x,a) = dest_exists xa
	val x' =  variant (form_frees b) x
	val a' = subst_form [(x',x)] a
	val xa'_conj = mk_exists (x',mk_conj (b,a'))
   in
	FCONV_OF
	   (let
		val (B,XA) = CONJ_PAIR (ASSUME xa_conj)
	    in
		CHOOSE (x',XA) (EXISTS (xa'_conj,x') (CONJ B (ASSUME a')))
	    end)
	   (let
		val (B,A') = CONJ_PAIR (ASSUME (mk_conj (b,a')))
	    in
		CHOOSE (x',ASSUME xa'_conj) (CONJ B (EXISTS (xa,x') A'))
	    end)
   end handle 
	syntax => raise general with "CONJ_EXISTS_FCONV" ||
	rule => raise general with "CONJ_EXISTS_FCONV";

val EXPAND_DISJ_FCONV =
   FIRST_FCONV [DISJ_IMP_FCONV,DISJ_CONJ_FCONV,CONJ_DISJ_FCONV];

val EXPAND_EXISTS_FCONV =
   FIRST_FCONV [EXISTS_IMP_FCONV,EXISTS_CONJ_FCONV,CONJ_EXISTS_FCONV];

(* (A<=>B) <=> (A==B /\ B==>A) *)
fun EXPAND_IFF_FCONV a_iff_b =
   let
	val (a,b) = dest_iff a_iff_b
   in
	FCONV_OF (IFF_CONJ (ASSUME a_iff_b))
		(CONJ_IFF (ASSUME (mk_conj (mk_imp (a,b),mk_imp (b,a)))))
   end handle 
	syntax => raise general with "EXPAND_IFF_FCONV" ||
	rule => raise general with "EXPAND_IFF_FCONV";

fun BASIC_FCONV conv fconv =
   TOP_DEPTH_FCONV
	(TOP_DEPTH_CONV conv)
	   (FIRST_FCONV
	    [fconv,BASIC_TAUT_FCONV,EXPAND_DISJ_FCONV,EXPAND_EXISTS_FCONV]);

fun LOCAL_BASIC_FCONV conv fconv = 
   LOCAL_TOP_DEPTH_FCONV
	(TOP_DEPTH_CONV conv)
	(FIRST_FCONV
	   [fconv,BASIC_TAUT_FCONV,EXPAND_DISJ_FCONV,EXPAND_EXISTS_FCONV]);

