(***************************************************************************
*
*	FCONV
*
****************************************************************************
* Original : fconv (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Rewriting primitives for formulas
*)

type fconv = form -> thm;



(* conversions for a theorem |- !x1 .. xn. A <=> B *)
val REWRITE_FCONV = (PART_FMATCH (fst o dest_iff));


(*	x == y
	-----------
	p x <=> p y
*)
fun MK_PRED (sym,argth) = 
   let
	val (x,y) = dest_equiv (concl argth)
  in
	mk_thm (hyp argth,mk_iff (mk_pred (sym,x),mk_pred (sym,y)))
   end handle syntax => raise rule with ("MK_PRED",[argth]);

(*		A <=> B
	[A,B]	C <=> D
	----------------
	 A/\C <=> B/\D
*)

fun MK_CONJ (abth,cdth) =
   let
	val (a,b) =dest_iff (concl abth)
	and (c,d) = dest_iff (concl cdth)
	and (abimp,baimp) = CONJ_PAIR (IFF_CONJ abth)
	and (cdimp,dcimp) = CONJ_PAIR (IFF_CONJ cdth)
	fun HALF (p,q) (pimp,qimp) =
	   let
		val pq = mk_conj (p,q)
		val (P,Q)=CONJ_PAIR (ASSUME pq)
		val P' = MP pimp P 
	   in
		DISCH pq (CONJ P' (CUT P (CUT P' (MP qimp Q))))
	   end
   in
	CONJ_IFF
	   (CONJ (HALF (a,c) (abimp,cdimp))
		 (HALF (b,d) (baimp,dcimp)))
   end handle 
	syntax => raise rule with ("MK_CONJ",[abth,cdth]) ||
	rule => raise rule with ("MK_CONJ",[abth,cdth]);

(*		A <=> B
		C <=> D
   -----------------------------------
	A\/C 	   <=>	    B\/D
*)
fun MK_DISJ (abth,cdth) = 
   let
	val (a,b) = dest_iff (concl abth)
	and (c,d) = dest_iff (concl cdth)
   in
	(mk_thm (union (hyp abth) (hyp cdth),
	 mk_iff (mk_disj (a,c) , mk_disj(b,d))))
   end handle syntax => raise rule with ("MK_DISJ",[abth,cdth]);

(*		A <=> B
	[A,B]	C <=> D
	------------------------
	A==>C   <=>   B==>D
*)
fun MK_IMP (abth,cdth) = 
   let 
	val (a,b) = dest_iff (concl abth)
	and (c,d) = dest_iff (concl cdth)
	and (abimp,baimp) = CONJ_PAIR (IFF_CONJ abth)
	and (cdimp,dcimp)= CONJ_PAIR (IFF_CONJ cdth)
	fun HALF (p,q) (p',q') (p'impp,qimpq') =
	   let
		val pq = mk_imp (p,q)
		and P = UNDISCH p'impp
	   in
		DISCH pq (DISCH p' (CUT P (MP qimpq' (MP (ASSUME pq) P))))
	   end
   in
	CONJ_IFF
	  (CONJ (HALF (a,c) (b,d) (baimp,cdimp))
		(HALF (b,d) (a,c) (abimp,dcimp)))
   end handle 
	rule => raise rule with ("MK_IMP",[abth,cdth]) ||
	syntax => raise rule with ("MK_IMP",[abth,cdth]);
		

(*		A <=> B
		C <=> D
	---------------------------
	A <=> C   <=>   B <=> D
*)
fun MK_IFF (abth,cdth) =
   let
	val (a,b) = dest_iff (concl abth)
	and (c,d) =dest_iff (concl cdth)
   in
	(mk_thm (union (hyp abth) (hyp cdth),
	 mk_iff (mk_iff (a,c),mk_iff (b,d))))
   end handle syntax => raise rule with ("MK_IFF",[abth,cdth]);

(*		(!x. A <=> B)
	--------------------------------
	(!x.A)	   <=>	   (!x.B)
*)
fun MK_FORALL bodyth =
   let
	val (x,body) = dest_forall (concl bodyth)
	val (a,b) = dest_iff body
   in
	mk_thm (hyp bodyth,mk_iff (mk_forall (x,a),mk_forall(x,b)))
   end handle syntax => raise rule with ("MK_FORALL",[bodyth]);

(*		(!x A <=> B)
	---------------------------
	(?x.A)		<=>   (?x.B)
*)

fun MK_EXISTS bodyth =
   let
	val (x,body) =dest_forall (concl bodyth)
	val (a,b) = dest_iff body
   in
	mk_thm (hyp bodyth,mk_iff (mk_exists (x,a),mk_exists (x,b)))
   end handle syntax => raise rule with ("MK_EXISTS",[bodyth]);


fun FSYM abth = 
   let
	val (a,b) = CONJ_PAIR (IFF_CONJ abth)
  in
	CONJ_IFF (CONJ b a)
   end handle rule => raise rule with ("FSYM",[abth]);

fun  FTRANS (abth,bcth) =
   let
	val (a,b) = dest_iff (concl abth)
	val (b',c) = dest_iff (concl bcth)
   in
	if aconv_form b  b' then
	   (mk_thm (union (hyp abth) (hyp bcth),mk_iff (a,c)))
	else raise rule with ("FTRANS",[abth,bcth])
   end handle 
	rule => raise rule with ("FTRANS",[abth,bcth])  ||
	syntax => raise rule with ("FTRANS",[abth,bcth]);
infix FTRANS;

(* formula conversion that always fails *)
val NO_FCONV : fconv = fn x=>raise rule with ("NO_FCONV",[]);

(* A -> |- A <=> A *)
fun ALL_FCONV a = mk_thm ([],mk_iff (a,a));
   


(* apply two conversions in succession, fail if either does *)
fun THENFC (fconv1,fconv2) : fconv =
  fn w =>
   let
	val th1=fconv1 w
	val th2 = fconv2 (snd (dest_iff (concl th1)))
   in
	th1 FTRANS th2
   end;

infix THENFC;

(* apply fconv1, if it fails, apply fconv2 *)
fun ORELSEFC (fconv1,fconv2) : fconv =
   fn w => fconv1 w handle 
		 syntax => fconv2 w ||
		 rule => fconv2 w ||
		 general => fconv2 w;

infix ORELSEFC;

(* perform first successful conversion of those in the list *)
fun FIRST_FCONV fconvl fm =
  itlist (curry (op ORELSEFC)) fconvl NO_FCONV fm handle 
		 syntax => raise general with "FIRST_FCONV" ||
		 rule => raise general with "FIRST_FCONV" ||
		 general => raise general with "FIRST_FCONV";

(* perform every conversion in the list *)
fun EVERY_FCONV fconvl fm =
   itlist (curry (op THENFC)) fconvl ALL_FCONV fm handle 
		 syntax => raise general with "EVERY_FCONV" ||
		 rule => raise general with "EVERY_FCONV" ||
		 general => raise general with "EVERY_FCONV";

(* apply a conversion zero or more times *)
fun REPEATFC fconv w =
   ((fconv THENFC (REPEATFC fconv)) ORELSEFC ALL_FCONV) w;

(* conversion fails if it causes no change *)
fun CHANGED_FCONV fconv fm = 
   let
	val th = fconv fm 
	val (l,r) = dest_iff (concl th)
   in
	if aconv_form l r then raise general with "CHANGED_FCONV"
	else th
   end;

fun TRY_FCONV fconv = fconv ORELSEFC ALL_FCONV;

(* apply a conversion to the body of a quantified formula, using
   genvar in case the conversion introduces the original bound variable.
   the replace the genvar with a variant of the original variable,
   necessary to avoid confronting the user with genvars in the result*)
fun QUANT_FCONV fconv (bv,body) = 
  let
	val gv = genvar (type_of bv)
	val bodyth = fconv (subst_form [(gv,bv)] body)
	val bv' = variant (thm_frees bodyth) bv 
   in
	GEN bv' (INST [(bv',gv)] bodyth)
   end;

fun CONJ_FCONV fconv fm =
  let
	val (left,right) = dest_conj fm
   in
	MK_CONJ (fconv left,fconv right)
   end;

fun DISJ_FCONV fconv fm =
   let
	val (left,right) = dest_disj fm
   in
	MK_DISJ (fconv left,fconv right)
   end;

fun IMP_FCONV fconv fm = 
   let
	val (left,right) = dest_imp fm
   in
	MK_IMP (fconv left,fconv right)
   end;

fun IFF_FCONV fconv fm =
   let
	val (left,right) = dest_iff fm
   in
	MK_IFF (fconv left,fconv right)
   end;

fun FORALL_FCONV fconv fm =
	MK_FORALL (QUANT_FCONV fconv (dest_forall fm));

fun EXISTS_FCONV fconv fm =
   MK_EXISTS (QUANT_FCONV fconv (dest_exists fm));

(* apply a term conversion to a predicate formula *)
fun PRED_FCONV conv fm =
   let
	val (sym,arg) = dest_pred fm
   in
	MK_PRED (sym,conv arg)
   end;

(* convert all top-level parts of a formula, uses "if" insted of ORELSEFC *)
fun SUB_FCONV conv fconv fm =
   if is_conj fm then CONJ_FCONV fconv fm
   else if is_disj fm then DISJ_FCONV fconv fm
   else if is_imp fm then IMP_FCONV fconv fm
   else if is_iff fm then IFF_FCONV fconv fm
   else if is_forall fm then FORALL_FCONV fconv fm 
   else if is_exists fm then EXISTS_FCONV fconv fm
   else PRED_FCONV conv fm;

(* apply a conversion recursively to a formula and its parts, the abstraction
   around w avoids infinite recusion, loops if the conversion function
   fconv never fails *)
fun DEPTH_FCONV conv fconv fm =
  (SUB_FCONV conv (DEPTH_FCONV conv fconv) THENFC (REPEATFC fconv)) fm;

(* like DEPTH_FCONV, but retraverses formula after each conversion, loops
    if the conversion function never fails*)
fun REDEPTH_FCONV conv fconv fm =
    (SUB_FCONV conv (REDEPTH_FCONV conv fconv) THENFC
	((fconv THENFC (REDEPTH_FCONV conv fconv)) ORELSEFC ALL_FCONV)) fm;


fun TOP_DEPTH_FCONV conv fconv fm = 
   (REPEATFC fconv THENFC
   	(TRY_FCONV
	   (CHANGED_FCONV (SUB_FCONV conv (TOP_DEPTH_FCONV conv fconv)) THENFC
	  	TRY_FCONV (fconv THENFC (TOP_DEPTH_FCONV conv fconv))))) fm;


(* local formula conversion for implications, it converts A==>B by using
    fconv to convert A to A2, then building a new conversion to convert
    B to B2, the new conversion is fconv_fun applied to A2*)
fun LOCAL_IMP_FCONV fconv fconv_fun fm =
   let
	val (left,right) = dest_imp fm 
	val lth = fconv left 
	val left2 = snd (dest_iff (concl lth)) 
	val fconv2 = if left2 = falsity then ALL_FCONV 
		     else fconv_fun (ASSUME left2)
   in
	MK_IMP (lth,fconv2 right)
   end;


(* local formula converions for conjunctions A/\B *)
fun LOCAL_CONJ_FCONV fconv fconv_fun fm =
   let
	val (left,right) = dest_conj fm
	val lth = fconv left
	val left2 = snd (dest_iff (concl lth))
	val fconv2 = if left2 = falsity then ALL_FCONV
		     else fconv_fun (ASSUME left2)
   in
	MK_CONJ (lth,fconv2 right)
   end;

(* local versions of SUB_CONV, uses local assumptions for implications and
   conjunctions *)
fun LOCAL_SUB_FCONV conv fconv fconv_fun fm =
   if is_disj fm then DISJ_FCONV fconv fm
   else if is_iff fm then IFF_FCONV  fconv fm
   else if is_forall fm then FORALL_FCONV fconv fm
   else if is_exists fm then EXISTS_FCONV fconv fm
    else if is_conj fm then LOCAL_CONJ_FCONV fconv fconv_fun fm
    else if is_imp fm then LOCAL_IMP_FCONV fconv fconv_fun fm 
   else PRED_FCONV conv fm;

(* local version of TOP_DEPTH_FCONV *)
fun LOCAL_TOP_DEPTH_FCONV conv fconv fconv_fun =
   let
	fun tdepth_fconv fm =
	   (REPEATFC fconv THENFC
		TRY_FCONV
		   ((CHANGED_FCONV
			(LOCAL_SUB_FCONV conv tdepth_fconv fconv_fun))
		     THENFC TRY_FCONV (fconv THENFC tdepth_fconv))) fm
   in
	tdepth_fconv
   end;

(*	A
  --------------
  A <=> TRUTH()
*)
fun IFF_TRUTH th =
	CONJ_IFF (CONJ (DISCH (concl th) TRUTH) (DISCH truth th));

(*	~A
  ------------------
   A <=> FALSITY()
*)
fun IFF_FALSITY th =
   let
	val (ante,conc) = dest_imp (concl th)
   in
	CONJ_IFF (CONJ th (DISCH falsity (CONTR ante (ASSUME falsity))))
   end handle 
	syntax => raise rule with ("IFF_FALSITY",[th]) ||
	rule => raise rule with ("IFF_FALSITY",[th]);

(* put a theorem
	|- A1 ==> A2 ==> ... => Am ==> B
into canonical form for formula conversions
	if B is C<=>D then leave as is
	if B is a negated predicate -P(x), replace it with P(x) <=> FALSITY()
	for predicates except TRUTH FALSITY ==, replace B with B <=> TRUTH()
	otherwise fail*)
fun FCONV_CANON th =
   let
	val w = concl th
   in
	if is_imp w then
	   let
		val (ante,conc) = dest_imp w
	   in
		if (conc = falsity) andalso (is_pred ante) then IFF_FALSITY th
		else DISCH ante (FCONV_CANON (UNDISCH th))
	   end
	else if is_iff w then th		
	else if is_pred w andalso
		(not (mem (fst (dest_pred w)) ["FALSITY","equiv"])) then
		  IFF_TRUTH th
	else raise rule with ("FCONV_CANON",[th])
   end;

(* conversion for a theorem |- ~A, taken to mean |- A <=> FALSITY() *)
val FALSITY_FCONV =
  (REWRITE_FCONV o IFF_FALSITY o GSPEC);

(* forward proof rule for conversions:
	A
   -----------   where fconv A is A<=>B
	B 
*)
fun FCONV_RULE fconv =
   fn th => MP(CONJUNCT1 (IFF_CONJ (fconv (concl th)))) th;

(* tactic for conversion:
	A
   ============ where fconv A is A<=> B
	B
*)

fun FCONV_TAC fconv : tactic = 
   fn (asl,w) =>
	let
	   val th2 = CONJUNCT2 (IFF_CONJ (fconv w))
	   val (ante,conc) = dest_imp (concl th2)
   	in
	   if ante = truth then ([],fn [] => MP th2 TRUTH)
	   else ([(asl,ante)],fn [th] => MP th2 th)
	end;


(*Must be hidden from users!!*)
val mk_thm = ();
