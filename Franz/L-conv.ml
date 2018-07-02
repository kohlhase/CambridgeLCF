(****************************************************************************
*
*	CONV
*
*****************************************************************************
* Original: conv (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
*)

type conv = term -> thm;

(* instantiate terms and types of  a theorem *)
fun INST_TY_TERM (substl,insttyl) th = 
   INST substl (INST_TYPE insttyl th);

(* |- !x y z. w -> |- w[g1/x] [g2/y] [g3/z] *)
fun GSPEC th =
   let
	val (w1,w) = dest_thm th
   in
	if is_forall w then
	GSPEC (SPEC (genvar (type_of (fst (dest_forall w)))) th)
	else th
   end;

(* match a given part of th to a formula, instantiating th, the part should
   be free in the theorem, except for outer bound variables *)
fun PART_FMATCH partfn th =
   let
	val pth = GSPEC (GEN_ALL th)
	val pat = partfn (concl pth)
	val match = form_match pat
   in
	fn fm => INST_TY_TERM (match fm) pth
   end;

(* matching modus ponens for implications of the form |- !x1 .. xn. P ==> Q 
   matches x1 .. xn : |- P' -> |- Q' 
   matches all types in conclusion except those mentioned in hypothesis *)
fun MATCH_MP impth =
   let
	val match = PART_FMATCH (fst o dest_imp) impth handle 
	   syntax => raise rule with ("MATCH_MP",[impth]) ||
	   rule   => raise rule with ("MATCH_MP",[impth])
   in
	fn th => MP (match (concl th)) th
   end;

(* match a given part of th to a theorem, instantiating th
   the part should be free in the theorem, except for outer bound variables*)
fun PART_TMATCH partfn th =
   let
	val pth = GSPEC (GEN_ALL th) 
	val pat = partfn (concl pth)
 	val match = term_match pat
   in
	fn t => INST_TY_TERM (match t) pth
   end;

(* conversion for rewrite rules of the form |- !x1 .. xn. t == u
   matches x1 .. xn :  t' -> |- t' == u
   matches all types in conclusion except those mentioned in hypothesis *)
val REWRITE_CONV = PART_TMATCH (fst o dest_equiv);

(* eta-conversion, \x. f x == f *)
val ETA_CONV = REWRITE_CONV ETA_EQ;

(* conversion that always fails, identity element for ORELSEC *)
val NO_CONV : conv = fn _ => raise general with "NO_CONV";
   
(* converion that always succeeds, using refexive law : t ---> |^t==t*)
val ALL_CONV = REFL;


(* apply two conversions in succession, fail if either does*)
fun THENC (conv1,conv2) : conv = 
  fn t =>
   let
	val th1 = conv1 t
	val th2 = conv2 (rhs (concl th1))
   in
	th1 TRANS th2
   end;

infix THENC;

(* apply conv1, if it fails then apply conv2*)
fun ORELSEC (conv1,conv2) : conv =
   fn t => conv1 t handle rule => conv2 t ||
			  syntax => conv2 t ||
			  general => conv2 t;

infix ORELSEC;

(* perform the first successful conversion of those in the list*)
fun FIRST_CONV convl tm =
   (itlist  (curry (op ORELSEC)) convl NO_CONV tm) handle 
	rule => raise general with "FIRST_CONV" ||
	general => raise general with "FIRST_CONV";


(* perform every conversion in the list *)
fun EVERY_CONV convl tm =
   (itlist (curry (op THENC)) convl ALL_CONV tm) handle 
		rule => raise general with "EVERY_CONV" ||
		general => raise general with "EVERY_CONV" ||
		syntax => raise general with "EVERY_CONV";

fun REPEATC conv t = ((conv THENC (REPEATC conv)) ORELSEC ALL_CONV) t;

(* cause the conversion to fail if it does not change its input*)
fun CHANGED_CONV conv tm = 
   let
	val th = conv tm
	val (l,r) = dest_equiv (concl th)
   in
	if aconv_term l r then raise general with "CHANGED_CONV" else th
  end

fun TRY_CONV conv = conv ORELSEC ALL_CONV;


(* apply conv to all top-level subterms of term*)
fun SUB_CONV conv tm =
   if is_comb tm then
	let
	   val(rator,rand) = dest_comb tm
	in
	   MK_COMB (conv rator,conv rand)
	end
  else if is_abs tm then
	let
	   val (bv,body) = dest_abs tm
	   val gv = genvar (type_of bv)
	   val bodyth = conv (subst_term [(gv,bv)] body)
	   val bv' = variant (thm_frees bodyth) bv 
	in
	   MK_ABS (GEN bv' (INST [(bv',gv)] bodyth))
	end
  else (ALL_CONV tm);


(* apply a conversion recursively to a term and its parts *)
fun DEPTH_CONV conv t =
   (SUB_CONV (DEPTH_CONV conv) THENC (REPEATC conv)) t;

(* like DEPTH_CONV, but retraverses term after each conversion, loops
  if the conversion never fails *)
fun REDEPTH_CONV conv t =
   (SUB_CONV (REDEPTH_CONV conv) THENC
	((conv THENC (REDEPTH_CONV conv)) ORELSEC ALL_CONV)) t;

(* rewrite the term t trying conversions at top level before descending, not 
  true normal order evaluation but may terminate where REDEPTH_CONV would
  loop, moore effecient than REDEPTH_CONV for rewrites that throw away 
  many of their pattern variables*)
fun TOP_DEPTH_CONV conv t =
   (REPEATC conv THENC (TRY_CONV
	(CHANGED_CONV (SUB_CONV (TOP_DEPTH_CONV conv)) THENC
	  TRY_CONV (conv THENC TOP_DEPTH_CONV conv)))) t;

(* slower, simpler version *)
(*  10/10/86
fun TOP_DEPTH_CONV conv t =
   (REPEATC conv THENC
	SUB_CONV (TOP_DEPTH_CONV conv) THENC
	   ((conv THENC TOP_DEPTH_CONV conv) ORELSEC ALL_CONV)) t;	
*)
