
(******************************************************************************
*
*		STRUCTAC
*
*******************************************************************************
* Original : structac (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. 1986
*
* Structural induction tactic.
* To exploit flatness or finiteness, accepts a list of theorems stating
* type properties, such as
*	FLAT {: 'a}  ==>  FLAT {:'a list}
* When applied to a goal, the tactic instantiates the types necessary,
* then "undischarges" all antecedents. For a list of truth values this gives:
*	[FLAT {:tr}] - FLAT {tr: list}
* which is a form that INDUCTS expects. Here, FLAT{:'a} stands for the expanded
* formula:
*	!x y: 'a. x<<y ==> UU==x \/ x==y
*)

fun dest_cons (x::l) = (x,l);

fun uncurry f (x,y) = f x y;

(* if ty' is an instance of ty, returns the instantiation of type variables
   - currently assumes that the types args of ty are distinct variables
   - a proper type_match is already coded in the lisp file L-simpl 
*)
fun type_match ty ty' =
   let
	val (oper,args) = dest_type ty
	val (oper',args') = dest_type ty'
   in
	if oper = oper' then args' com args else 
		raise general with "type_match"
  end handle syntax  => raise general with "type_match";

(* gets basic parts of a structure from its CASES axiom *)
fun get_struct_parts cases_ax =
   let
	val (sty,caseforml) = (type_of // disjuncts) (dest_forall (concl cases_ax))
	val (varsl,bodyl) = split (map strip_exists (tl caseforml))
	val (eql,defhypsl) = split (map (dest_cons o conjuncts) bodyl)
	val conl = map (fst o strip_comb o rhs) eql
  in
	(sty,conl,varsl,defhypsl)
   end;

(* solves bottom case of computation induction*)
fun BOTTOM_TAC (var,uucase) = 
   let
	val sty = type_of var
   in
	EVERY [X_GEN_TAC var,
	       SUBSTl_TAC (SPEC var (INST_TYPE [(sty,`: 'a`),(sty,`: 'b`)] MIN_COMB)),
	       ACCEPT_TAC uucase]
   end;
(* implication elimination*)
fun MP_TAC thb : tactic = 
    fn (asl,w) => ([(asl,mk_imp(concl thb,w))],fn [thimp] => MP thimp thb);

(* expand all cases of the definition of the copying functionals, put conjoined
   defidness hypothesis as antecedent. *)
fun FUN_CASES_TAC (var,indvar,varsl,cases_ax,funax_conj) =
   let
	val sty = type_of var
   in
	X_CASES_THENL ([]::varsl)
	   (map (fn (vars,ax) => fn conjth =>
			(let
			   val (eqth::defhyps) = CONJUNCTS conjth
			in
			   SUBSTl_TAC eqth THEN
			   SUBSTl_TAC (LIST_MP defhyps (SPECL (indvar::vars) ax))
			   THEN 
				MP_TAC (LIST_CONJ 
				    (TRUTH::(filter (fn th =>
					not(sty = (type_of o lhs o fst o      
						dest_imp o concl) th))
					        defhyps)))
			end)) (* end fn *)
		(([]::varsl) com (CONJUNCTS funax_conj))) (* end map *)
	    (SPEC var cases_ax)
   end;

(* generates structural induction hypotheses from the computation one,
   for each variable of the structure's type - these are conjoined into
   single antecedent *)
fun INDHYP_TAC (indvar,indhyp) vars =
     EVERY[MP_TAC TRUTH,
	EVERY
	   (mapfilter (fn v =>
		let 
		   val vhyp = SPEC v indhyp
		in
		   EVERY[DISCH_THEN (MP_TAC o (CONJ vhyp)),
		         SPEC_TAC (mk_comb (indvar,v),v),
			 X_GEN_TAC v] end) vars),
	DISCH_THEN (MP_TAC o LIST_CONJ o rev o CONJUNCTS)];

(* for sorting definedness hyps in oreder of variables *)
fun find_defhyp defthms v =
   find (fn th => (concl th) = `~ ^v==UU`) defthms;

(* proves UU for strict, recursive structure variables - merges resulting
   definedness hyps with those for non-recirsive variables, and sorts
   them in the proper order - resulting goals have the form:
	defhyps ==> indhyps ==> A(constr) *)
fun STRICT_TAC (uucase,def_cases_lemma) (strict_lemma,svars) = 
   DISCH_THEN (fn indhyps =>
	EVERY
	   (mapfilter (fn (ax,v) =>
		let
		   val defcases = SPEC v def_cases_lemma
		in
		   DISJ_CASES_THEN2
			(fn uu =>
			  EVERY [DISCH_TAC,SUBSTl_TAC uu,
				 SUBSTl_TAC ax,ACCEPT_TAC uucase])
			(fn defth =>
			   DISCH_THEN (MP_TAC o (CONJ defth)))
			defcases
		 end)
	     (filter (is_equiv o concl) (CONJUNCTS strict_lemma) com svars))
	THEN
	DISCH_THEN (fn defconj =>
		MP_TAC indhyps THEN
		MP_TAC
		   (LIST_CONJ
			(TRUTH::(map(find_defhyp (CONJUNCTS defconj)) svars)))));


(*				!x.A(x)
	------------------------------------------------------------
		(TRUTH() ==> TRUTH () ==> A(UU))
		(TRUTH() ==> TRUTH() ==> A(TIP))
		(!a t. (TRUTH() /\ ~a==UU /\ =t==UU) ==>
			(TRUTH() /\ A(t)) ==>
			A(UNIT a t ))
		(!b t tl.
			(TRUTH() /\ =b==UU /\ =t==UU /\ =tl==UU) ==>
			(TRUTH() /\ A(t) /\ A(tl)) ==>
			A(BRANCH b t tl)
*)
fun BASIC_STRUCT_TAC thy =
   (let
	val cases_ax = axiom thy "CASES"
	and funax_conj = axiom thy "COPY_FUN"
	and fixfunax = axiom thy "WELL_FOUNDED"
	and strictax = axiom thy "STRICT"
	and def_cases_lemma = theorem thy "DEF_CASES"
   	
	val (sty,_,varsl,defhypsl) = get_struct_parts cases_ax
	val strictvarsl = map (map (lhs o fst o dest_imp)) defhypsl
   in
     fn ty_thms =>
	fn (asl,w) =>
	   (let
		val (bv,body) = dest_forall w handle syntax => 
			   raise tactic with
		    ("BASIC_STRUCT_TAC: goal not quantified",[(asl,w)])
		val sty' = type_of bv
		val indvar = genvar `:^sty' -> ^sty'`
		val instl = type_match sty sty'  handle general =>
		   raise tactic with
		    ("BASIC_STRUCT_TAC: wrong type for induction",[(asl,w)])
		val INSTTY = INST_TYPE instl
		val goalfrees = forml_frees (w::asl)
		val bv' = variant goalfrees bv
		val vary = (variant (bv'::goalfrees)) o (inst_term [] instl)
		val varsl' = map (map vary) varsl
		val svarsl' = map (map vary) strictvarsl
		val fixfunax' = INSTTY fixfunax
		val funcon = 
   		   snd(dest_comb(fst(dest_comb
				(lhs(snd(dest_forall(concl fixfunax')))))))
           in
		(X_GEN_TAC bv' THEN
		SUBST_TAC [SYM (SPEC bv' fixfunax')] THEN
		SPEC_TAC (bv',bv') THEN
		SUBGOAL_THEN
		   (mk_imp (truth,mk_imp (truth,subst_form[(`UU: ^sty'`,bv)] body)))
		(fn uucase0 =>
		   (let
			val uucase = MP (MP uucase0 TRUTH) TRUTH
		   in
			INDUCT_TAC (map (UNDISCH_ALL o INSTTY)ty_thms)
			           [(funcon,indvar)]
			THENL
			[BOTTOM_TAC (bv',uucase),
			 X_GEN_TAC indvar THEN
			DISCH_THEN
			  (fn indhyp =>
			   	X_GEN_TAC bv' THEN
				FUN_CASES_TAC
				   (bv',indvar,varsl',INSTTY cases_ax,
				    INSTTY funax_conj)
				THENL
				   ((DISCH_TAC THEN ACCEPT_TAC uucase)::
				   (map (INDHYP_TAC(indvar,indhyp)) varsl')))
				THENL
				   (let
					val strictl =
					   map (uncurry SPECL)
						(varsl' com
						 (CONJUNCTS
						   (INSTTY strictax)))
				    in
					map
					  (STRICT_TAC (uucase,
							INSTTY def_cases_lemma))
					   (strictl com svarsl')
				     end)
				THENL (* put quantifiers on *)
				  (map (MAP_EVERY (fn v =>
					SPEC_TAC (v,v)) o rev)
				       varsl')
			   ] 
			end)))
		   (asl,w)
	  end)
  end);
			

(*	TRUTH() /\ A1 /\ .. /\ An ==> B
   -----------------------------------------
		[A1, ... ,An] B
*)
val DISCH_HYPS_TAC =
   DISCH_THEN (fn hypconj => MAP_EVERY CUT_THM_TAC (tl (CONJUNCTS hypconj)));

(*			... !x . A(x)
    -----------------------------------------------------------------
		   	A (UU)
			A (TIP)
	[~ a==UU, ~ t==UU, A(t)] A(UNIT a t)
	[~ b==UU,~ t==UU, ~ tl==UU, A(t),A(tl)] A(BRANCH b t tl)
induction tactic for interactive use - splits up the goal - inducts on the
 subformula !z. A, puts subgoals int sensible form - curried so that it
will do some work if applied just to "thy" *)
fun STRUCT_TAC thy =
   let
	val STAC = BASIC_STRUCT_TAC thy
	fun temp ty_thms x =
		EVERY[REPEAT (FILTER_GEN_TAC x ORELSE FILTER_DISCH_TAC x),
		      STAC ty_thms,REPEAT GEN_TAC,DISCH_HYPS_TAC,
		      DISCH_HYPS_TAC]
   in
	   temp		
   end;

   



	       
