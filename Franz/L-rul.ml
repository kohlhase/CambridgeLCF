(*****************************************************************************
*
*	RUL
*
*******************************************************************************
* Original: rul (Cambridge LCF)
* Inference rules for substitution and induction 
*)


fun hyp_union thl =
   itlist union (map hyp thl) [];

(* given [|-"ti == ui",xi] A(xi)

	ti == ui   A(ti)
	-----------------
	     A(ui)
*)
fun SUBST thvars w lhsthm =
   let
	val (ths,vars) = split thvars
	val (ls,rs) = split (map (dest_equiv o concl) ths)
   in
	if aconv_form (subst_form (combine (ls,vars)) w) (concl lhsthm) then
	   mk_thm (hyp_union (lhsthm::ths), subst_form (combine (rs,vars)) w)
	else raise general with ""
   end handle syntax => raise rule with ("SUBST",[lhsthm]);

(*
	ti == ui	A(ti)
	---------------------
		A(ui)
*)
fun GSUBS substfn ths th =
   let
      val instl = map (fn th => 
		let val (x,y)=dest_equiv(concl th) in (y,x) end) ths
      val hyps = hyp_union (th::ths)
   in
	mk_thm (hyps,substfn instl (concl th))
   end;


fun SUBS ths th = (GSUBS subst_form ths th) handle syntax => 
		raise rule with ("SUBS",[th]);

fun SUBS_OCCS nlths th =
   let
	val (nll,ths) = split nlths 
   in
	(GSUBS (subst_occs_form nll) ths th ) handle syntax => 
		raise rule with ("SUBS_OCCS",[th])
  end;

fun BETA_CONV t =
   let  val (f,v) = dest_comb t 
	val (x,u) = dest_abs f
   in  mk_thm ([],`^t == ^(subst_term[(v,x)] u)`)
   end
   handle syntax => raise general with "BETA_CONV";

	

(* ADMISSIBILITY OF FIXED-POINT INDUCTION
   **************************************
 *)


fun terms_of_form (fm, tms) =
    if is_conj fm then
	let val (A,B) = dest_conj fm 
	in terms_of_form (A, terms_of_form (B, tms))  end
    else if is_disj fm then
	let val (A,B) = dest_disj fm 
	in terms_of_form (A, terms_of_form (B, tms))  end
    else if is_imp fm then
	let val (A,B) = dest_imp fm 
	in terms_of_form (A, terms_of_form (B, tms))  end
    else if is_iff fm then
	let val (A,B) = dest_iff fm 
	in terms_of_form (A, terms_of_form (B, tms))  end
    else if is_forall fm then
	let val (_,A) = dest_forall fm 
	in terms_of_form (A, tms)  end
    else if is_exists fm then
	let val (_,A) = dest_exists fm 
	in terms_of_form (A, tms)  end
    else (*predicate*)
	let val (_,t) = dest_pred fm 
	in t::tms  end;


(* return type that has been proved finite, type * is finite if:
	|- !x:'a. x==cl \/ ... \/ x==cn   where ci are constants *)
fun finite_type th =
   let
	val (bv,body) =  dest_forall (concl th)
	val ty = type_of bv
   in
	if forall (fn (lh,rh) => (lh : term) = bv andalso is_const rh)
		  (map dest_equiv (disjuncts body)) 
	 then ty
	 else raise general with "finite_type"
   end handle syntax => raise general with "finite_type";
	      

(* return the type that has been proved chain-finite. Type is chain-finite if
	|- !x1 ... xn . x1<<x2 /\ ... /\ x[n-1]<<xn ==>
	   UU==x1 \/ ... \/ x[n-1]<<xn *)
fun cfinite_type th = 
   let
	val ((bv::bvs),body) =  strip_forall (concl th)
				(* bind could be raised here *)
	val ty = type_of bv
	val (ante,conc) = dest_imp body
   in
	let
	   val (als,ars) = split (map dest_inequiv (conjuncts ante))
	   val ((cl::cls),(cr::crs)) = split (map dest_equiv (disjuncts conc))
	in
	   if ars = bvs andalso als = (bv::(rev (tl (rev ars))))
		andalso cl = `UU:^ty` andalso cr = bv andalso cls = als
		andalso crs = ars andalso distinct (bv::bvs)
	   then ty
	   else raise general with "cfinite_type"
        end
   end handle 
	bind => raise general with "cfinite_type" ||
	syntax => raise general with "cfinite_type";

(* the type constructors fun, prod preserve finiteness *)
fun is_finite finite_types ty =
   mem ty finite_types orelse 
   (if is_vartype ty then false
    else 
	let
	   val (opp,args) = dest_type ty
	in
	   mem opp ["fun","prod"] andalso
	   forall (is_finite finite_types) args
	end);

(* finite types are chain-finite, prod preserves chain-finiteness, 
   ty -> ty2 is chain-finite if
   ty1 is finite and ty2 is chain-finite *)
fun is_cfinite ty_props ty =
   (let
	val (cfinite_types,finite_types) = ty_props
   in
	mem ty cfinite_types orelse
	mem ty finite_types orelse
	(if is_vartype  ty then false
	 else
	   (let
		val (opp,args) = dest_type ty
	    in
		if opp = "fun" then
		   (let
			val [dom,range] = args
		   in
			is_finite finite_types dom andalso
			is_cfinite ty_props range
		   end)
		else
		   if opp = "prod" then forall (is_cfinite ty_props) args
	  	   else false
	     end) (* end let *)
	   )(* end if *)
   end) (* let *);


(* test if a given occurrence of a term is free in the induction formula.*)
fun all_global (globals,tm) = forall(fn v => mem v globals) (term_frees tm);

(* see if tm is the constant UU of any type *)
fun is_uu tm  = is_const tm andalso (fst (dest_const tm) = "UU");



(* A term is admissible if:
   it does not mention the induction variable x or
   its type is chain-finite and it is free in the induction formula or
   its subterms are all admissible. *)
fun admits_tm ty_props x =
   (let
	fun ad_tm globals tm =
	   (is_cfinite ty_props (type_of tm) andalso all_global (globals,tm))
	 orelse
	   (if is_const tm then true else
	    if is_var tm then not (tm = x) else
	    if is_abs tm then
		let
		   val (bv,body) = dest_abs tm
		in
		   bv = x orelse ad_tm (subtract globals [bv]) body     
		end else
	     if is_comb tm then
		let
		   val (rator,rand) = dest_comb tm
		in
		   ad_tm globals rator  andalso ad_tm globals rand
		end
	    else syserror "admits_tm" )
   in
	ad_tm
   end);


(*admissibility by chain-finiteness: all terms must be admissible*)
fun admits_fm_cf ty_props x fm =
    let val globals = form_frees fm
    in  forall (admits_tm ty_props x globals) (terms_of_form (fm,[]))
    end;


fun admits_pred ty_props x (pos,fm) =
    if pos then
	(is_equiv fm orelse is_inequiv fm) orelse  admits_fm_cf ty_props x fm
    else
	(is_inequiv fm andalso  not (term_freein_term x (rhs fm))) orelse
	(is_equiv fm   andalso (is_uu (lhs fm) orelse is_uu (rhs fm))) orelse
	admits_fm_cf ty_props x fm;	       

 
(* Admissibility of formulas:
	disjunction and conjunction preserve admissibility
	forall (and ~exists) preserve admissibility
	finite quantifications preserve admissibility
	A ==> B is admissible if ~A and B are
	A <=> is regarded as A==>B /\ B==> A *)
fun admits_fm ty_props x =
    let val (cfinite_types,finite_types) = ty_props;
        fun ad_fm (pos,fm) = 
	    let fun ad_quant  (good, (bv,body)) =
		      bv = x orelse
		       (if good  orelse  is_finite finite_types (type_of bv)
			then ad_fm (pos,body)
		        else admits_fm_cf ty_props x fm);
		fun ad_conn p (left,right) =
	              ad_fm (p,left) andalso ad_fm (p,right)
	    in
	       if is_conj fm then ad_conn pos (dest_conj fm) else
	       if is_disj fm then ad_conn pos (dest_disj fm) else
	       if is_imp fm then
	    	let val (left,right) = dest_imp fm
	    	in
	    	   ad_fm (not pos,left) andalso
	    	   ad_fm (pos,right)
	    	end else
	       if is_iff fm then
	    	ad_conn pos (dest_iff fm) andalso
	    	ad_conn (not pos) (dest_iff fm) else
	       if is_forall fm then ad_quant (pos, (dest_forall fm)) else
	       if is_exists fm then ad_quant (not pos, (dest_exists fm)) else
	       if is_pred fm then admits_pred ty_props x (pos,fm)
	       else syserror "admits_fm"
	    end
   in ad_fm
   end;
		



fun admits_induction ty_thms fm x =
   let val ty_props =
	(mapfilter cfinite_type ty_thms, mapfilter finite_type ty_thms)
   in
	is_var x  andalso  admits_fm ty_props x (true,fm)
   end;

val uu_pairs = map (fn x=>(mk_const ("UU",type_of x), x));
val step_pairs = map (fn (ff,x) => (mk_comb (ff,x),x));
val map_fix = map (fn ff => `FIX ^ff`);


(* Induction rule, reformulated to use universal quantifier the Bi state that 
  certain types are chain-finite or finite, for admissibility:
	B1 ... Bn A[UU]    !f1 ... fn. A[fi] ==> A[funi fi]
    ---------------------------------------------------------
		A[FIX funi]
*)

fun INDUCT funs ty_thms (thuu,thstep) =
   let
	val (vars,step) = strip_forall (concl thstep)
	val (w,step_conc) =  dest_imp step
   in
	if forall (admits_induction ty_thms w) vars andalso
	   distinct vars andalso
	   aconv_form (concl thuu) (subst_form (uu_pairs vars) w) andalso
	   aconv_form step_conc (subst_form (step_pairs (combine (funs,vars)))w)
	then
	   mk_thm (hyp_union(thuu::thstep::ty_thms),
			subst_form (combine(map_fix funs,vars)) w)
	else raise syntax with ""
   end handle syntax => raise rule with ("INDUCT",thuu::thstep::ty_thms);


