(*******************************************************************************
*
*	TACTICS
*
*******************************************************************************
* Original: tactics (Cambridge LCF)
* Tactics inverting the inference rules, and other basic tactics.
*)

(* accepts a theorem that satisfies the goal*)
fun ACCEPT_TAC th (asl,w) = 
   if aconv_form (concl th) w then ([],fn [] => th)
   else raise tactic with ("ACCEPT_TAC",[(asl,w)]);

(* checks tat a theorem is useless, then ignores it *)
fun DISCARD_TAC th (asl,w) =
   if exists (aconv_form (concl th)) (truth::asl) then ALL_TAC(asl,w)
   else raise tactic with ("DISCARD_TAC",[(asl,w)]);


(* contradiction rule*)
fun CONTR_TAC cth (asl,w) = 
  let val th = CONTR w cth in ([],fn [] => th) end
  handle rule => raise tactic with ("CONTR_TAC",[(asl,w)]);

(* put a theorrm on the assumtion list.
  Note: since an assumtion B denotes a theorem B|-B you cannot instantiate
  types or variable in assumtions.
*)
fun CUT_THM_TAC bth (asl,w) = ([(((concl bth)::asl),w)],fn [th] => CUT bth th)

(* freeze a theorem to prevent instantiation*)
fun FREEZE_THEN ttac bth = 
   fn g => let val (g1,prf) = ttac (ASSUME (concl bth)) g in
		(g1,CUT bth o prf)
	    end;

(* disjunction introduction*)
fun DISJ1_TAC (asl,w) = 
   let
	val (a,b) = dest_disj w 
   in
	([(asl,a)],fn [tha] => DISJ1 tha b)
   end;


fun DISJ2_TAC (asl,w) =
   let
	val (a,b) = dest_disj w
   in
	([(asl,b)],fn [thb] => DISJ2 a thb)
   end;

(* bi-implication introduction
   A==>B     B==>A
  ----------------
	A<=>B       *)
fun IFF_TAC (asl,w) = 
   let
	val (a,b) = dest_iff w
   in
	([(asl,`^a==> ^b`),(asl,`^b==> ^a`)],
	  fn [thab,thba] => CONJ_IFF (CONJ thab thba))
   end handle 
	syntax => raise tactic with ("IFF_TAC",[(asl,w)]) ||
	rule => raise tactic with ("IFF_TAC",[(asl,w)]);

(* universal introduction
  explicit version for tactic programming, proof fails if x is free in hyps.
*)
fun X_GEN_TAC x' (asl,w) =
   let
	val (x,body) = dest_forall w
   in
	([(asl,subst_form [(x',x)] body)],fn [th] => GEN x' th)
   end handle syntax => raise tactic with ("X_GEN_TAC",[(asl,w)]);

(* chooses a variant for the user, for interactive proof *)
fun GEN_TAC (asl,w) = 
   let
	val (x,body) = dest_forall w handle syntax => raise tactic with
					("GEN_TAC",[(asl,w)])
   in
	X_GEN_TAC (variant (forml_frees (w::asl)) x) (asl ,w)
   end;

(*Specialization
      !x.A(x)
  ---------------- 
 	A(t)
example of use: generalizing a goal before attempting an interactive proof
as with Boyer and Moore.
Valid only if x is not free in A(UU),
*)
fun SPEC_TAC (t,x) (asl,w) =
   ([(asl,mk_forall (x,subst_form [(x,t)] w))],fn [th] => SPEC t th)
    handle syntax => raise tactic with ("SPEC_TAC",[(asl,w)]);


(* existential introduction*)
fun EXISTS_TAC t (asl,w) =
  let
	val (x,body) = dest_exists w
   in
	([(asl,subst_form [(t,x)] body)], fn [th] => EXISTS (w,t) th)
   end handle syntax => raise tactic with ("EXISTS_TAC",[(asl,w)]);


(* Computation induction. for admissibility includes TR_CASES

		A(FIX funi)
	======================================== ty_thms [funi,fi]
	A(UU)    !f1 .. fn. A(fi) ==> A(funi fi)

*)
val uu_pairs = map (fn x => (mk_const("UU",type_of x), x))
and step_pairs = map (fn (ff,x) => (mk_comb(ff,x), x))
and map_fix = map (fn ff => `FIX ^ff`);

fun INDUCT_TAC ty_thms0 funfs : tactic =
 fn (asl,w) =>
   let
	val ty_thms = TR_CASES::ty_thms0
	val (funs,fs) = split funfs 
	val indfm = subst_form (fs com (map_fix funs)) w
   in
	if not (forall (admits_induction ty_thms indfm) fs) then raise tactic 
	      with ("INDUCT_TAC: does not admit induction",[(asl,w)])
	 else ();
	let
	   val wuu = subst_form (uu_pairs fs) indfm
	   val wstep = list_mk_forall (fs,
		mk_imp (indfm,subst_form (step_pairs (funs com fs)) indfm))
	in
	   ([(asl,wuu),(asl,wstep)],
		fn [thuu,thstep] => INDUCT funs ty_thms (thuu,thstep))
	end
   end;
   
(* substitution: these substitute in the goal, thus they DO NOT invert
  the rules SUBS and SUBS_OCCS, despite superficial similarities. In fact,
  SUBS and SUBS_OCCS are not invertiable; only subst is.
*)
fun GSUBST_TAC substfn ths : tactic =
  fn (asl,w) =>
   let
	val (ls,rs) = split (map (dest_equiv o concl) ths)
	val vars =  map (genvar o type_of) ls
	val base = substfn (combine (vars,ls)) w
   in
	([(asl,subst_form (combine (rs,vars)) base)],
	 fn [th] => SUBST (combine (map SYM ths,vars)) base th)
   end;

fun SUBST_TAC ths = GSUBST_TAC subst_form ths;

fun SUBST_OCCS_TAC nlths = 
  let val (nll,ths) = split nlths in GSUBST_TAC (subst_occs_form nll) ths end;


(*Substitution by one theorem*)
fun SUBSTl_TAC rthm = SUBST_TAC [rthm];

(* map an inference rule over the assumptions, replacing them *)
fun RULE_ASSUM_TAC rule =
   POP_ASSUM_LIST (fn asl => MAP_EVERY CUT_THM_TAC (rev (map rule asl)));

(*substitute throughout the goal and its assumptioms *)
fun SUBST_ALL_TAC rth =
   SUBSTl_TAC rth THEN RULE_ASSUM_TAC (SUBS [rth]);

fun CHECK_THM_TAC gth = 
   FIRST [CONTR_TAC gth,ACCEPT_TAC gth,DISCARD_TAC gth,CUT_THM_TAC gth];

val STRIP_THM_TAC  = (REPEAT_TCL STRIP_THM_THEN) CHECK_THM_TAC;

(* give a theorem

  |- (?y1. x==t1 (y1 /\ B1 (x,y1)) \/ ... \/ (?yn. x==tn(yn) /\ Bn(x,yn))

  each y is a vector of zero or more variables, and each Bi is a conjunction
 (Cil /\ ... /\ Cin)

	[Cil (tm,yl')] A(t1) ... [Cin(tm,yn')] A(tn)
	-------------------------------------------
			A(x)

 such definitions specify a structure as having n different possible
 constructions (the ti) from subcomponents (the yi) that satisfy various
 constraints (ther Cij).
*)
val STRUCT_CASES_TAC =
   REPEAT_TCL STRIP_THM_THEN (fn th => SUBSTl_TAC th ORELSE CUT_THM_TAC th);

(* find a conditional `p=>t|u` that is free in the goal and whose condition p
  is not a constant, perform a cases split on the condition 

	A(p=>t|u)
  ===================
    [p==UU] A(UU)
    [p==TT] A(t)
    [p==FF] A(u)
*)
val COND_CASES_TAC : tactic = 
  fn (asl,w) =>
  let
      fun is_good_cond_aux (p,_,_) = not(is_const p)
      fun is_good_cond tm =
		is_good_cond_aux (dest_cond tm) handle syntax => false
      val cond = 
	find_term_in_form (fn tm => is_good_cond tm andalso term_freein_form tm w) w
      val (p,t,u) = dest_cond cond 
      val condcl = 
         CONJUNCTS (SPECL [t,u] (INST_TYPE [(type_of t ,`: 'a`)] COND_CLAUSES))
   in
	REPEAT_TCL DISJ_CASES_THEN
	  (fn th => SUBSTl_TAC th THEN SUBST_TAC condcl THEN CUT_THM_TAC th)
	  (SPEC p TR_CASES) (asl,w)
   end;

(* cases on p==UU \/ p==TT \/ p==FF *)
fun TR_CASES_TAC p =
   STRUCT_CASES_TAC (SPEC p TR_CASES);

val CONJ_TAC : tactic =
   fn (asl,w) =>
	let
	   val (l,r) = dest_conj w
	in
	   ([(asl,l),(asl,r)],fn [th1,th2] => CONJ th1 th2)
	end handle syntax => raise tactic with ("CONJ_TAC",[(asl,w)]);

(* strip one outer !, /\, ==> from the goal *)
fun STRIP_GOAL_THEN ttac =
  FIRST [GEN_TAC,CONJ_TAC,DISCH_THEN ttac];

(* like GEN_TAC but fails if the term equals the quantified variable *)
fun FILTER_GEN_TAC tm : tactic  =
fn (asl,w) =>
   if is_forall w andalso not (tm = fst (dest_forall w)) then
  	GEN_TAC (asl,w)
    else raise tactic with ("COND_CASES_TAC",[(asl,w)])
	
(* like DISCH_THEN but fails if the antecendent mentions the term *)
fun FILTER_DISCH_THEN ttac tm : tactic =
  fn  (asl,w) =>
   if is_imp w andalso not (term_freein_form tm (fst (dest_imp w))) then
	DISCH_THEN ttac (asl,w)
   else raise tactic with ("FILTER_DISCH_THEN",[(asl,w)]);

(* like STRIP_THEN but preserves any part of hte goal that mention the goal *)
fun FILTER_STRIP_THEN ttac tm =
   FIRST [FILTER_GEN_TAC tm,FILTER_DISCH_THEN ttac tm,CONJ_TAC];


val DISCH_TAC = DISCH_THEN  CUT_THM_TAC;
val DISJ_CASES_TAC = DISJ_CASES_THEN CUT_THM_TAC;
val CHOOSE_TAC = CHOOSE_THEN  CUT_THM_TAC;
fun X_CHOOSE_TAC x = X_CHOOSE_THEN  x  CUT_THM_TAC;
val STRIP_TAC = STRIP_GOAL_THEN STRIP_THM_TAC;
val FILTER_DISCH_TAC = FILTER_DISCH_THEN STRIP_THM_TAC;
val FILTER_STRIP_TAC = FILTER_STRIP_THEN STRIP_THM_TAC;




(*NEW TACTICS FOR SEQUENT CALCULUS: OPERATE ON ASSUMPTIONS*)



(*tactic for cut rule*)
fun CUT_TAC (A:form) (asl,B) =
  ([ (asl,A), (A::asl,B) ] , fn[thA,thB] => CUT thA thB);

fun ACCEPT_ASM_TAC (asl,A) : goal list * proof =
    if (exists (aconv_form A) asl) then ([], fn[]=> ASSUME A)
    else raise tactic with ("ACCEPT_ASM_TAC", [(asl,A)]);

(*maps [x1,...,xn] to ( [xi], [x1,...,x(i-1), x(i+1),..,xn])  where xi 
  is first member satisfying the predicate p.
  If none satsify p then returns ([], [x1,...,xn])  *)
fun take_first p xs = 
  let fun take (rxs, []) = ([], rev rxs)
        | take(rxs, x::xs) = 
            if p(x) then ([x], rev rxs @ xs)
            else take(x::rxs, xs)
  in take([],xs) end;


(*tactic for conjunction-left: splits a conjunctive assumption in two*)
fun CONJ_LEFT_TAC (asl,C) : goal list * proof =
    case  take_first is_conj asl  of
       ([asm], asl') =>
           let val (A,B) = dest_conj asm;
               val conjth = ASSUME asm
           in  ([(A::B::asl',C)], 
                fn[th] => CUT (CONJUNCT1 conjth) (CUT (CONJUNCT2 conjth) th))
           end
     | _ => raise tactic with ("CONJ_LEFT_TAC", [(asl,C)]);


(*tactic for disjunction-left: case split on a disjunctive assumption*)
fun DISJ_LEFT_TAC (asl,C) : goal list * proof =
    case  take_first is_disj asl  of
       ([asm], asl') =>
           let val (A,B) = dest_disj asm
           in  ([(A::asl',C), (B::asl',C)], 
                fn[thA,thB] => DISJ_CASES (ASSUME asm) thA thB)
           end
     | _ => raise tactic with ("DISJ_LEFT_TAC", [(asl,C)]);


(*tactic for implication-left: for assumption A==>B, prove A and use B*)
fun IMP_LEFT_TAC (asl,C) : goal list * proof =
    case  take_first is_imp asl  of
       ([asm], asl') =>
           let val (A,B) = dest_imp asm
           in  ([(asl'@[asm],A), (B::asl',C)], 
                fn[thA,thB] => CUT (MP (ASSUME asm) thA) thB)
           end
     | _ => raise tactic with ("IMP_LEFT_TAC", [(asl,C)]);


(*test that C has the form !x.C' for given variable, x *)
fun isvar_forall x C =
    is_forall C andalso
	let val (y,_) = dest_forall C in x=y end;

(*tactic for forall-left: instantiate universal assumption*)
fun FORALL_LEFT_TAC (t,x) (asl,C) : goal list * proof =
    case  take_first (isvar_forall x) asl  of
       ([asm], _) =>
           let val specth = SPEC t (ASSUME asm)
           in  ([(concl specth :: asl, C)], 
                fn[th] => CUT specth th)
           end
     | _ => raise tactic with ("FORALL_LEFT_TAC", [(asl,C)]);

(*tactic for exists-left: use existential assumption*)
fun EXISTS_LEFT_TAC (asl,C) : goal list * proof =
    case  take_first is_exists asl  of
       ([asm], asl') =>
           let val (x,A) = dest_exists asm;
               val x' = variant (forml_frees(C::asl)) x;
               val A' = subst_form [(x',x)] A
           in  ([(A'::asl',C)], 
                fn[th] => CHOOSE (x', ASSUME asm) th)
           end
     | _ => raise tactic with ("EXISTS_LEFT_TAC", [(asl,C)]);
