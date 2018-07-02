(******************************************************************************
*
*	PCRULE
*
*******************************************************************************
* Original: pcrule (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Predicates Calculus rules for LCF. These form a classical Gentzen Natural 
* Deduction System.
*)

(* syntax functions for formula lists *)
val (forml_frees,forml_vars,forml_tyvars) =
   let 
	fun ff f wl = itlist (fn w => union (f w)) wl nil
   in
	(ff form_frees,ff form_vars, ff form_tyvars)
   end;

(* free varibles of a theorem *)
fun thm_frees th = forml_frees (concl th :: hyp th);

(* discharge all assumptions w from w1 *)
fun disch (w,w1) = filter (fn w' => not (aconv_form w w')) w1;

(* Conjunction *)

(* intro:
    		A	B
		----------
		  A /\ B
*)
fun CONJ th1 th2 =
   mk_thm (union (hyp th1) (hyp th2),mk_conj (concl th1, concl th2));

(* elim:
		   A/\B
		----------
		A	B
*)
fun CONJUNCT1 th =
   mk_thm (hyp th,fst (dest_conj (concl th))) handle syntax => 
		raise rule with ("CONJUNCT1",[th])

fun CONJUNCT2 th =
   mk_thm (hyp th,snd (dest_conj (concl th))) handle syntax => 
		raise rule with ("CONJUNCT2",[th])

(* Disjunction *)

(* intro :
		A		B
	   ----------      ------------
	     A \/ B	      A \/ B
*)
fun DISJ1 th w = mk_thm(hyp th, mk_disj(concl th, w));

fun DISJ2 w th = mk_thm(hyp th,mk_disj (w, concl th));

(* elim:
	  	A \/ B 	A|- C	B|- C
	   -------------------------------
			  C
*)
fun DISJ_CASES dth ath bth =
   if is_disj (concl dth) andalso aconv_form (concl ath) (concl bth) then
	let
	   val (lw,rw) = dest_disj (concl dth)
	in
	   mk_thm (union (hyp dth)
			(union (disch (lw,hyp ath)) (disch (rw,hyp bth))),
		   concl ath)
	end
   else raise rule with ("DISJ_CASES",[dth,ath,bth]);
	
(* Implication *)

(* intro:
		A |- B
		------
		A => B
*)
fun DISCH w th = mk_thm(disch (w,hyp th),mk_imp(w,concl th));

(*elim:
	A ==> B		A
	-----------------
	         B
*)
fun MP thi th =
   let
	val (wa,wc) = dest_imp (concl thi) 
   in
	if aconv_form wa (concl th) then
	   mk_thm(union (hyp thi) (hyp th),wc)
	else raise rule with ("MP",[thi,th])
   end handle syntax => raise rule with ("MP",[thi,th]) ||
	      general => raise rule with ("MP",[thi,th]);

(* there are no rules for negation since ~P is merely an abbreviation for
   P ==> FALSITY. Formally, if-and-only-if is also an abrrev. But it names
  its arguments twice, it is implemented as a separate syntactic class, with
  inference rules mapping P <=> Q to the conjunction (P ==> Q) /\ (Q ==> P);
*)

(* if-and-only-if  *)
		
(* intro:
		(A ==> B) /\ (B ==> A)
		----------------------
		       A <=> B
*)
fun CONJ_IFF th =
   let
	val (lw,rw) = dest_conj (concl th)
	val (la,lc) = dest_imp lw 
	val (ra,rc) = dest_imp rw
   in
	if aconv_form la rc andalso aconv_form lc ra then
	   mk_thm(hyp th,mk_iff (la,lc))
        else raise rule with ("CONJ_IFF",[th])
   end handle syntax => raise rule with ("CONJ_IFF",[th]) ;

(* elim:
		A <=> B
	  -----------------------
	   (A ==> B) /\ (B ==> A)
*)
fun IFF_CONJ th =
   let
	val (lw,rw) = dest_iff (concl th) 
   in
	mk_thm(hyp th,mk_conj (mk_imp (lw,rw),mk_imp(rw,lw)))
   end handle syntax => raise rule with ("IFF_CONJ",[th]);

(* universal quantifier *)

(* intro:
        A               variable "x" not free in assumptions
    ---------
      !x.A                   *)
fun GEN x th =
   if exists (term_freein_form x) (hyp th) then
	raise general with ""
   else
	mk_thm (hyp th,mk_forall (x,concl th))
   handle 
	syntax => raise rule with ("GEN",[th]) ||
	general => raise rule with ("GEN",[th]);

(* elim:
		!x.A[x]
	     --------------
		  A[t]
*)
fun SPEC t th =
   let 
  	val (x,w) = dest_forall (concl th)
   in
	mk_thm (hyp th,subst_form[(t,x)] w)
    end handle syntax => raise rule with ("SPEC",[th]);

(* existential quantifier *)

(* intro :
		A[t]
	   --------------
	      ?x.A[x]
The argument w shows what form the conclusion should take. This is helpful
because the theorem |- TT==TT could be used to prove ?p. p==TT, ?. TT=p
or ?p. p==p.
*)
fun EXISTS (w,t) th =
   let
	val (x,body) = dest_exists w
   in
	if aconv_form (subst_form [(t,x)] body) (concl th) then
	   mk_thm (hyp th, w)
	else
	   raise general with ""
   end handle syntax => raise rule with ("EXISTS",[th]) ||
	     general => raise rule with ("EXISTS",[th]);

(* elim:
		X.A(X)		[A(a)] B
		------------------------
			  B
The variable a must not be free in either premiss, except in B's 
hypothesis of the form A(a)
*)
fun CHOOSE (y,thA) thB =
   let val (x,A) = dest_exists (concl thA)
       val bhyp = disch (subst_form [(y,x)] A, hyp thB)
   in
      if not (is_var y)
      orelse exists (term_freein_form y)
           ((concl thA::hyp thA) @ (concl thB::bhyp))
      then raise rule with ("CHOOSE",[thA,thB])
      else mk_thm (union (hyp thA) bhyp, concl thB)
   end handle syntax => raise rule with ("CHOOSE",[thA,thB]);


(* other inference rules *)

(* assumption:
		---------------
		     [A] A
*)
fun ASSUME w = mk_thm([w],w);

(* contradiction 
		FALSITY
	   ----------------
		   A
*)
fun CONTR w fth =
   if concl fth = falsity then mk_thm (hyp fth,w) else 
		raise rule  with ("CONTR",[fth]);


(* Classical contradiction rule (allows to assume negation of conclusion 
		~A |- FALSITY
		-------------
		     A
*)
fun CCONTR w fth =
   if concl fth = falsity then
	mk_thm (disch (mk_imp (w,falsity),hyp fth),w)
   else
	raise rule with ("CCONTR",[fth]);


(* instantiate types in a theorem *)
fun INST_TYPE [] th = th |
    INST_TYPE inst_tylist th = 
	let
	   val (asl,w) = dest_thm th
	   val tyvl = map ((assert is_vartype) o snd) inst_tylist
	in
	   if exists (fn ty => exists (type_in_form ty) asl) tyvl then
		raise general with ""
	   else
		mk_thm (asl,inst_form (forml_frees asl) inst_tylist w)
	end handle syntax => raise rule with ("INST_TYPE",[th]) ||
	           general=> raise rule with ("INST_TYPE",[th]);
   
(* instantiate variables in a theorem *)
fun INST [] th = th |
    INST inst_list th =
	let
	   val (asl,w) = dest_thm th
	   val vars = map (assert is_var o snd) inst_list
	in
	   if exists (fn var => exists (term_freein_form var) asl) vars then
		raise general with ""
	   else
		mk_thm (asl,subst_form inst_list w)
	end handle syntax => raise rule with ("INST",[th]) ||
	           general=> raise rule with ("INST",[th]);

(* Make a theorem that assumes falsity. A legitimate way for the user
   to make a theorem of any form, for testing of derived inference rules. 
   Most rules won't notice the extra assumption, strong though it is*)
fun mk_fthm (asl,w) = mk_thm (falsity::asl,w);


