(******************************************************************************
*
*	STRUCTAXM
*
*******************************************************************************
* Original : structaxm (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
*
* Structural Induction Package
* Builds a theory for a recursive structure with lazy constructor functions.
*)

(* ([ty1,...,tyn],ty) -> :ty1 -> (ty2 -> .. -> tyn)) *)
fun list_mk_funtype (arg_tys,ty) = 
   itlist 
     	(let
	   fun temp aty ty = `:^aty -> ^ty`
	in
	   temp
	end) arg_tys ty;

(* declare a constant or infix, return it *)
fun new_const (name,typ) =
   let
	val (c::cl) = explode name
   in
	if c= "$" then
	   let
		val iname = implode cl
	   in
		 new_curried_infix (iname,typ); mk_const (iname,typ)
	   end
	else
	   (new_constant (name,typ);mk_const (name,typ))
   end;

(* check that names do not contain primes and are distinct in their groups *)
fun prime_free tok = forall (fn ch => not (ch = "'")) (explode tok);
fun check_names (contokl,varsl) =
   let
	val namesl = contokl::(map (map (fst o dest_var)) varsl) handle
			syntax => raise general with 
			"check_names: non-variable in tuple"
   in
	if not (forall distinct namesl) then
	   raise general with "check_names: identifiers not distinct"
	else if not (forall prime_free (flat namesl)) then
	   raise general with "check_names: identifiers must not contain primes"
 	else ()
   end;

(* (good_type sty ty) means that sty's type operator appears in ty only at
   top-level, with its original type variables - the only type variables
   in ty are those of sty *)
fun good_type sty =
   let
	val (styop,styvars) = dest_type sty
	fun nice ty =
		if is_vartype ty then (mem ty styvars)
	   	else
		   let
			val (tyop,tys) = dest_type ty
		   in
			not (tyop = styop ) andalso forall nice tys
		  end
   in
	fn ty => ty = sty orelse nice ty
   end;

(* check the types in the structure*)
fun check_var_types (sty,varsl) =
   let
	val (_,styvars) = dest_type sty
   in
	if not (forall is_vartype styvars andalso distinct styvars) then
	   raise general with
		"check_var_types: bad type variables in stucture"
	else
	   if not (forall ((good_type sty) o type_of) (flat varsl)) then
		raise general with "check_var_types: bad type of variable"
	else ()
   end;

fun get_strict_mode m =
   if m = "strict" then true
   else if m = "lazy" then false
   else raise general with 
	("get_strict_mode: illegal mode of variable " ^ m);

fun mk_defhyps modevars =
   itlist 
	(let
	   fun temp (mode,var) hyps =
		if mode then `~ ^var == UU`::hyps else hyps
	in
	   temp
	end) modevars [];

(* name used for variables of the structure - to avoid conflict, all internal 
   variables contain a prime - the user's identifiers may not contain primes *)
val absvar_name = "abs'";

(* build the cases axiom 
  !ABS
	ABS == UU \/
	ABS == TIP /\
	(?A T. ABS == UNIT A T /\ ~A ==UU /\ ~T ==UU \/
	  (?A T Tl. ABS == BRANCH A T TL /\ ~ A==UU /\ ~ T==UU /\ ~ Tl==UU)
*)

fun mk_cases_ax (varsl,constrl,defhypsl) =
   let
	val absvar = mk_var (absvar_name,type_of (hd constrl))
   in
     new_axiom ("CASES",
	mk_forall (absvar,
	   list_mk_disj (`^absvar == UU` ::
		(map list_mk_exists
		   (varsl com
			(map (fn (constr,hyps) =>
			   list_mk_conj (`^absvar==^constr`::hyps))
			(constrl com defhypsl)))))))
   end;

fun mk_copyfun_axpair (sty,conl,varsl,defhypsl) =
   let
	val funty = `:^sty -> ^sty`
	val funvar = `FP' : ^funty`
	and absvar = mk_var (absvar_name,sty)
	val (styop,_) = dest_type sty
	val funcon = new_const(styop ^ "'_FUN",`: ^funty -> ^funty`)
   in
	(new_axiom ("COPY_FUN",
	   list_mk_conj
		(map (fn (con,(vars,defhyps)) =>
			let
			   fun apf tm = mk_comb(funvar,tm) handle syntax => tm
			   val constr = list_mk_comb (con,vars)
			   val fconstr = list_mk_comb (con,map apf vars)
   			in
			   list_mk_forall (funvar::vars,
		list_mk_imp (defhyps,`^funcon ^funvar ^constr == ^fconstr`))
			end)
		(`UU:^sty` :: conl com ([]::varsl com []::defhypsl)))),
	 new_axiom ("WELL_FOUNDED", `!^absvar.FIX ^funcon ^absvar == ^absvar`))
   end;

(* (`UNIT a t`,[`a`,`t`]) -> [`UNIT UU t == UU`,`UNIT a UU == UU`]
   for non-strict variables returns TRUTH in the corresponding positions *)
fun mk_strict_forms (constr,modes) =
   let
	val (_,vars) = strip_comb constr 
   in
	map (fn (var,mode) =>
		if mode then
		   `^(subst_term [(mk_const ("UU",type_of var),var)] constr) == UU`
		else truth)
	(vars com modes)
   end;

(* make strictness axioms :
 	TRUTH() /\
	(!A T. TRUTH() /\ UNIT UU T == UU /\ UNIT A UU == UU) /\
	(!B T Tl. TRUTH() /\ BRANCH UU T Tl == UU /\
		BRANCH A UU Tl =- UU /\ BRANCH A T UU == UU)
*)
fun mk_strict_ax (constrl,varsl,modesl) =
   new_axiom ("STRICT",
     list_mk_conj
	(map (fn (vars,forms) =>
	   list_mk_forall (vars,list_mk_conj (truth::forms)))
	(varsl com (map mk_strict_forms (constrl com modesl)))));

(* definedness axiom :
	~TIP == UU /\
	(!A T. ~A==UU ==> ~T==UU ==> ~UNIT A T == UU) /\
	(!B T Tl. ~B==UU ==> ~T==UU ==> ~BRANCH B T Tl == UU)
*)
fun mk_defined_ax (constrl,defhypsl) =
   new_axiom ("DEFINED",
	list_mk_conj
	   (map (fn (constr,defhyps) =>
		gen_all (list_mk_imp (defhyps,`~ ^constr == UU`)))
	    (constrl com defhypsl)));

(* make axiom for relation between two constructors 	!A T Tl A' T'. ~A==UU ==> ~T==UU ==> ~Tl=UU ==>
   distinctness:
	~BRANCH A T Tl << UNIT A T
   invertability:
	!A T A' T'. ~A==UU ==> ~T==UU ==>		UNIT A T << UNIT A' T' ==> A<<A' /\ T<<T'
*)



(* prove invertability of equivalence 
	!A L A' L'.
	   ~A==UU ==> ~L==UU ==>
	~A' == UU ==> ~L'==UU ==>
	UNIT A T == UNIT A' T' => TRUTH() /\ A==A' /\ L==L' *)
fun prove_eq_inv (constr,(modes,LESS_INV)) =
   let
	val (con,vars) = strip_comb constr
	val vars' = map (variant vars) vars
	val (_::LESSL) = CONJUNCTS (UNDISCH_ALL (SPECL (vars @ vars') LESS_INV))
	val (_::LESSL') = CONJUNCTS (UNDISCH_ALL (SPECL (vars' @ vars) LESS_INV))
	val constr' = list_mk_comb (con,vars')
	val con_eq = `^constr == ^constr'`
	val hypshyps = mk_defhyps (modes com vars) @ mk_defhyps (modes com vars')
   in
	((itlist GEN (vars @ vars')) o
	(itlist DISCH hypshyps) o (DISCH con_eq) o
	(itlist CUT (CONJUNCTS (ANAL (ASSUME con_eq)))) o LIST_CONJ)
	(TRUTH::(map (fn (a,b) => SYNTH (CONJ a b)) (LESSL com LESSL')))
  end;

(*	~NIL << CONS a l
 -----------------------------------
   NIL == CONS a l <=> FALSITY
*)
fun prove_eq_falsity imp_th =
   let
	val (ante,conseq) =dest_imp (concl imp_th)
   in
	if conseq = falsity then
	   let
		val (l,r) = dest_inequiv ante
		val eqhyp = `^l == ^r`
	   in
		IFF_FALSITY
			(DISCH eqhyp
			   (MP imp_th (CONJUNCT1 (ANAL (ASSUME eqhyp)))))
	   end
	else raise general with "prove_eq_falsity"
   end;
				
(*	CONS a l == CONS a' l' ==> TRUTH /\ a==a' /\ l==l'
    ---------------------------------------------------------
	CONS a l == CONS a' l' <=> TRUTH /\ a==a' /\ l==l'
*)
fun prove_eq_same imp_th =
   let
	val (ante,conseq) = dest_imp (concl imp_th)
   in
	if is_imp conseq then raise general with "prove_eq_same"
	else
	   let
		val eq_thl = tl (CONJUNCTS (ASSUME conseq))
		val rvars = map (rhs o concl) eq_thl
	   in
		CONJ_IFF (CONJ imp_th
		   (DISCH conseq (SUBST (eq_thl com rvars) ante (REFL (lhs ante)))))
	   end
  end;

(* make a maximality goal
	!ABS . TIP << ABS ==> ABS == TIP

	!ABS A T. ~A ==UU ==> ~T =UU ==>
		UNIT A T <, ABS ==>
		(?A' T'. ABS ==UNIT A' T' /\ ~A'=UU /\ ~T'=UU)

	!ABS B T Tl. ~B ==UU ==> ~T==UU ==> ~Tl==UU ==>
		BRANCH B T Tl<<ABS =->
		 (?B' T' Tl'. ABS =- BRANCH B T Tl /\
		~B'==UU /\ ~T'==UU /\ ~Tl'==UU)
*) 
fun mk_max_goal (con,(modes,vars)) =
   let
	val vars' = map (variant vars) vars
	val constr = list_mk_comb (con,vars)
	val constr' = list_mk_comb(con,vars')
	val (contok,_) = dest_const con
   in
	let
	   val absvar = mk_var (absvar_name,type_of constr)
	in
	   ([],
	   list_mk_forall (absvar::vars,
	 	list_mk_imp(mk_defhyps (modes com vars),
		mk_imp (`^constr << ^absvar`,
		   list_mk_exists (vars',
			list_mk_conj (`^absvar == ^constr'`::
			   mk_defhyps (modes com vars')))))))
	end
   end;

(* solves goal that assumes [abs<<UU] *)
fun UU_TAC def_axiom =
   (ASSUM_LIST (CUT_THM_TAC o (tryfind LESS_UU_RULE)) THEN
	CONTR_TAC (UNDISCH_ALL (SPEC_ALL def_axiom)));

(* tactic for all the constructor relations axioms - proves goals that
   assume `constr1<<constr2` by CONTR_TAC and goals `?x.constr x== constr y`
   by EXISTS_TAC *)
fun CONREL_TAC vars (rel_ax,gvars) =
   (CONTR_TAC (UNDISCH_ALL (SPECL gvars (SPECL vars rel_ax)))
   ORELSE
   (MAP_EVERY EXISTS_TAC gvars THEN FIRST_ASSUM ACCEPT_TAC));

(* solves a maximality goal *)
fun MAX_TAC (cases_ax,varsl) (def_axiom,(rel_ax_l,vars)) =
   let
	val gvarsl = map (map (genvar o type_of)) varsl
	and absvar = fst (dest_forall (concl cases_ax))
   in
	MAP_EVERY X_GEN_TAC (absvar::vars) THEN
	REPEAT DISCH_TAC THEN
	POP_ASSUM (fn lessth =>
		X_CASES_THEN ([]::gvarsl)
		   (fn caseth =>
			let
			   val (eqth::conjl) = CONJUNCTS caseth
			in
			   CUT_THM_TAC (SUBS [eqth] lessth) THEN
			   MAP_EVERY CUT_THM_TAC (caseth::conjl)
			end)
			(SPEC absvar cases_ax))
		THENL
		(UU_TAC def_axiom:: (map
			(CONREL_TAC vars) (rel_ax_l com gvarsl)))
   end;

(* states and proves maximality lemmas *)
fun prove_max_lemma (conl,modesl,varsl,cases_ax,defined_ax,conrel_ax_ll) =
   let
	val max_goal_l = map mk_max_goal (conl com (modesl com varsl))
	val MAX_TAC_L=
	   map (MAX_TAC (cases_ax,varsl))
		(CONJUNCTS defined_ax com (conrel_ax_ll com varsl))
   in
	save_thm ("MAXIMAL",
		LIST_CONJ (map TAC_PROOF (max_goal_l com MAX_TAC_L)))
   end

(* prove !ABS. ABS == UU \/ ~ABS == UU *)
fun prove_def_cases_lemma (cases_ax,defined_ax) =
   let
	val absvar = fst (dest_forall (concl cases_ax))
	val sty = type_of absvar
   in
	prove_thm ("DEF_CASES",
	   `!^absvar. ^absvar == UU \/ ~(^absvar == UU)`,
	   X_GEN_TAC absvar THEN
	 	STRUCT_CASES_TAC (SPEC absvar cases_ax) THENL
		((DISJ1_TAC THEN ACCEPT_TAC (REFL `UU: ^sty`))::
		(map (fn ax => EVERY [DISJ2_TAC,DISCH_TAC,
				CONTR_TAC(UNDISCH_ALL (SPEC_ALL ax))])
		 (CONJUNCTS defined_ax))))
    end;

(* predicate expressing flatness of the type of the variable x*)
fun flat_pred x =
   let
	val x' = variant [x] x 
   in
	`(!^x. !^x'. ^x << ^x' ==> UU==^x \/ ^x ==^x')`
   end;

(* make flatness hypotheses for all constructor variables, suppressing
   duplicate types and the structure type itself *)
fun flat_hyps (sty,varsl) =
   map flat_pred
	(snd (itlist 
	   (let
		fun temp v (tyl,vl) =
		   let val ty = type_of v in  if mem ty tyl then
				   (tyl,vl) else ((ty::tyl),(v::vl)) 
		   end
	   in
		temp
	   end)
	   (flat varsl)
	   ([sty],[])));

fun mk_flat_goal (sty,varsl) =
   let
	val (styop,styvars) = dest_type sty
	and absvar = mk_var (absvar_name,sty)
   in
	([],list_mk_imp (flat_hyps (sty,varsl),flat_pred absvar))
   end;

(*uses a consequence of flatness - if UU=x then proves contradiction
   - if y==x then then substitutes *)
val FLAT_CASES_TAC =
   DISJ_CASES_THEN2 
	(fn th => ANTE_RES_THEN CONTR_TAC (SYM th) THEN
	   FAIL_TAC "could not solve UU case")
	SUBSTl_TAC;

(* using maximality and invertability, invokes flatness of components of
   constructor, sending results to FLAT_CASES_TAC *)
fun FLAT_CONSTR_TAC maxvar (MAX,INV) =
   EVERY[ DISJ2_TAC,FIRST_ASSUM MP_TAC,
	STRUCT_CASES_TAC (UNDISCH_ALL (SPEC_ALL (SPEC maxvar MAX))),
	DISCH_TAC,
	MAP_EVERY (ANTE_RES_THEN FLAT_CASES_TAC)
	   (tl (CONJUNCTS (UNDISCH_ALL (SPEC_ALL INV))))];

(* tactic to prove flatness of the structure *)
fun FLAT_TAC (max_lemma,invert_lemma) =
   EVERY [REPEAT DISCH_TAC,
	(fn (asl,w) =>
		let
		   val ([var1,var2],_) = strip_forall w
		in
		   (STRUCT_TAC "-" [] var1 THEN
		   GEN_TAC THEN DISCH_TAC THENL
		  (DISJ1_TAC::
			(map (FLAT_CONSTR_TAC var2)
			   (CONJUNCTS max_lemma com CONJUNCTS invert_lemma)))) 
		end
		(asl,w)),
	MATCH_ACCEPT_TAC EQ_REFL];


fun mk_rel_ax (con,(modes,vars)) (con2,(modes2,vars2)) =
   let
	val vars' = map (variant vars) vars2
	val constr = list_mk_comb (con,vars)
	val constr2 = list_mk_comb (con2,vars')
	val (contok,_) = dest_const con
	val (contok2,_) = dest_const con2
   in
	let
	   val conc = 
		if con = con2 then
		   list_mk_conj (truth::(map (fn (v,v') => `^v << ^v'`)
					(vars com vars')))
		else falsity
	in
	   list_mk_forall (vars @ vars',
		list_mk_imp(mk_defhyps ((modes com vars) @
				        (modes2 com vars')),
			`^constr << ^constr2 ==> ^conc`))
	end
   end;

fun prove_flat_lemma (modesl,sty,varsl,max_lemma,invert_lemma) =
   save_thm ("FLAT",
	if forall I (flat modesl) then
	   (TAC_PROOF (mk_flat_goal (sty,varsl),
  	    FLAT_TAC (max_lemma,invert_lemma)))
	else TRUTH);

(* make a conjunction of all the constructor relation axioms for all
   possible pairs of constructors *)
fun mk_conrel_ax convars_list =
   new_axiom ("LESS",
	list_mk_conj
	   (map (fn cv => list_mk_conj (map (mk_rel_ax cv) convars_list))
	   convars_list));

fun struct_axm_main (sty,contokl,modesl,varsl) =
  let
	val _ = (check_names (contokl,varsl),check_var_types (sty,varsl))
	val (styop,styvars) = dest_type sty
	val defhypsl = map (mk_defhyps o combine) (modesl com varsl)
	val conl = 
	   let fun curryty vars = list_mk_funtype (map type_of vars,sty)
	   in
  		map new_const (contokl com (map curryty varsl)) 
	   end
	val constrl = map list_mk_comb (conl com varsl)
	val cases_ax = mk_cases_ax (varsl,constrl,defhypsl)
	val (funax_conj,fixfunax) = mk_copyfun_axpair (sty,conl,varsl,defhypsl)
	val strict_ax = mk_strict_ax (constrl,varsl,modesl)
	val defined_ax = mk_defined_ax (constrl,defhypsl)
	val conrel_ax = mk_conrel_ax (conl com (modesl com varsl))
	val conrel_ax_ll = map CONJUNCTS (CONJ_LIST (length conl) conrel_ax)
	val max_lemma =
	   prove_max_lemma (conl,modesl,varsl,cases_ax,defined_ax,conrel_ax_ll)
	val def_cases_lemma = prove_def_cases_lemma (cases_ax,defined_ax)
	val less_inv_l = diagonal conrel_ax_ll
	val eq_inv_lemma_l = map prove_eq_inv (constrl com (modesl com less_inv_l))
	val eq_iff_same_l = map (ONCE_DEPTH_CHAIN prove_eq_same) eq_inv_lemma_l
	val eq_iff_all_ll =
	   map (fn (axl,(diagax,eqth)) =>
		map (fn ax => if ax = diagax then eqth
				else ONCE_DEPTH_CHAIN prove_eq_falsity ax)
		axl)
	    (conrel_ax_ll com (diagonal conrel_ax_ll com eq_iff_same_l))
	val less_inv_lemma = save_thm ("LESS_INVERT",LIST_CONJ less_inv_l)
	val eq_inv_lemma = save_thm ("EQ_INVERT",LIST_CONJ eq_inv_lemma_l)
	val eq_iff_same = save_thm ("EQ_IFF_SAME",LIST_CONJ eq_iff_same_l)
	val eq_iff_all =
	   save_thm ("EQ_IFF_ALL",LIST_CONJ (map LIST_CONJ eq_iff_all_ll))
	val flat_lemma =
	   prove_flat_lemma (modesl,sty,varsl,max_lemma,less_inv_lemma)
   in
	()
   end;

(* general form , allows any combination of strict constructors:
	(`:('a,'b) tree,
	   [("TIP",[]),("UNIT",["strict",`A:'a`,"strict",`T:('a,'b) tree`]),
	   ("BRANCH",["strict",`B:'b`,"strcit",`T:('a,'b)tree`,"stict",
			`Tl:('a,'b)tree`])]);
*)
val gen_struct_axm =
  fn (sty,mode_arms_l) =>
   let
	val (contokl,modevarsl) = split mode_arms_l 
	val (mode_namesl,varsl) = split (map split modevarsl)
   in
	struct_axm_main (sty,contokl,map (map get_strict_mode) mode_namesl,varsl)
   end;

(* simple form, entire structure is either strict or lazy 
	(`:('a,'b)tree`,
	"strict",
	[("TIP",[]),("UNIT",[`A:'a`,`T:('a,'b)tree`]),
	("BRANCH",[`B:'b`,`T:('a,'b)tree`,`Tl:('a,'b)tree`])])
*)

val struct_axm =
  fn (sty,mode_name,armsl) =>
   let
	val (contokl,varsl) = split armsl
	val mode = get_strict_mode mode_name
   in
	struct_axm_main (sty,contokl,map (map (K mode)) varsl,varsl)
   end;
