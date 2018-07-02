(****************************************************************************
*
*	OL-NET
*
*****************************************************************************
* Original ol-net (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. 
*
* ML interface to lisp-coded ol network functions. These provide
* the ability to store obj indexed by terms or formulas, particulary
* for simplification.
*)

val nil_term_net = [];
fun enter_term (tm,dat) tnet =
   (enter_term_rep (dat,tm,tnet));
fun lookup_term tnet tm =
   lookup_term_rep (tnet,tm);
fun merge_term_nets tnet1 tnet2 =
   (merge_nets_rep (tnet1,tnet2));

val nil_form_net = [];
fun enter_form (fm,dat) fnet =
   (enter_form_rep (dat,fm,fnet));
fun lookup_form fnet fm =
   lookup_form_rep (fnet,fm);
fun merge_form_nets fnet1 fnet2 =
   (merge_nets_rep (fnet1,fnet2));




(* beta-conversion, paired with the appropriate pattern *)
val BETA_CONV2 = (`(\x: 'a.y: 'b ) z`, K BETA_CONV);

(* match a given part of 'th' to a formula - instantiating 'th', the part
   should be free in the theorem, except for outer bound variables
   - returns the pattern used for matching, and a function to match and 
   instantiate the theorem *)
fun PART_FMATCH2 partfn th =
   let
	val pth = GSPEC (GEN_ALL th)
        val pat = partfn (concl pth)
	val match = form_match pat
   in
	(pat,fn fm => INST_TY_TERM (match fm) pth)
   end;

(* match a given part of 'th' to a theorem, instantiating 'th' - the part
   should be free in the theorem, except for outer bound variables *)
fun PART_TMATCH2 partfn th =
   let
	val pth = GSPEC (GEN_ALL th)
	val pat = partfn (concl pth)
	val match = term_match pat
   in
	(pat,fn t => INST_TY_TERM (match t) pth)
   end;

(* conversion for implicative rewrites |-!x1 .. xn.A1 ==> .. ==> Am ==> t=u 
   - returns the pattern it matches, for building the net 
   - tries to prove the instantiated antecedents A1 .. An using the tactic
	if the tactic cannot do it, the conversion fails *)
fun IMP_REW_CONV2 irth : term * (tactic -> conv) =
   let  val (t,u) = (dest_equiv o snd o strip_imp o 
			snd o strip_forall o concl) irth;
	val (pat,matchfn) = 
		PART_TMATCH2 (fst o dest_equiv o snd o strip_imp)  irth;
	fun conv_of_tac (tac:tactic) tm =
	   let  val irth' = matchfn tm
		val (antel,_) = strip_imp (concl irth')
		val ANTEL =  map (fn w => TAC_PROOF(([],w),tac)) antel
	   in  LIST_MP ANTEL irth'  end
	   handle rule => raise general with "IMP_REW_CONV2"
               || tactic => raise general with "IMP_REW_CONV2"
    in
	if (can matchfn u) then raise general with 
		"IMP_REW_CONV2: rewriting would loop"
	else  (pat, conv_of_tac)
    end;

fun IMP_REW_FCONV2 irth =
   let  val (b,c) = 
	   (dest_iff o snd o strip_imp o snd o strip_forall o concl) irth;
	val (pat,matchfn) = 
	   PART_FMATCH2 (fst o dest_iff o snd o strip_imp) irth;
        fun conv_of_tac (tac:tactic) fm =
	    let val irth' = matchfn fm
		val (antel,_) = strip_imp (concl irth')	
		val th1 = map (fn w => TAC_PROOF (([],w),tac)) antel
	     in LIST_MP th1 irth'  end
	   handle rule => raise general with "IMP_REW_FCONV2"
               || tactic => raise general with "IMP_REW_FCONV2"
   in
	if (can matchfn c) then raise general with
		"IMP_REW_FCONV2: rewriting would loop"
	else  (pat, conv_of_tac)
   end;

(* use the theorem for term rewriting or formula rewriting if possible 
   - enter it into existing term/formula nets *)
fun use_rewrite_lemma th (cnet,fcnet) =
   let
	val can_th1 = IMP_CANON th
   in
     (rev_itlist enter_term (mapfilter IMP_REW_CONV2 can_th1) cnet,
      rev_itlist enter_form (mapfilter (IMP_REW_FCONV2 o FCONV_CANON) can_th1)
	   	   fcnet)
   end;

(* map_ap x [f1,..,fn] -> [f1 x,..,fn x] *)
fun map_ap x = map (fn f => f x);

(* rather ad-hoc functions for applying conversions stored in nets *)
fun FIRST_NET_CONV cnet tac tm =
   FIRST_CONV (map_ap tac (lookup_term cnet tm)) tm
and FIRST_NET_FCONV fcnet tac fm =
   FIRST_FCONV (map_ap tac (lookup_form fcnet fm)) fm;

(* main conversions for rewriting formulas - calls itself recursively
   to solve implicative rewrites and to introduce local assumptions *)
fun MAIN_REWRITE_FCONV (cnet,fcnet) =
   let
	fun tac g = FCONV_TAC fconv g
	and fconv fm =
	   LOCAL_BASIC_FCONV
		(FIRST_NET_CONV cnet tac)
		(FIRST_NET_FCONV fcnet tac)
		(fn th => MAIN_REWRITE_FCONV
			   (use_rewrite_lemma th (cnet,fcnet))) 
		fm
   in
	fconv
   end;

(* build discrimination nets containing the rewrite theorems *)
fun build_nets thms =
   rev_itlist use_rewrite_lemma thms
	(enter_term BETA_CONV2 nil_term_net,nil_form_net);

(* rewrite a formula using a list of theorems *)
val rewrite_form = MAIN_REWRITE_FCONV o build_nets;

(*rewrite a formula using a list of theorems *)
fun rewrite_term thms =
   let
	val (cnet,fcnet) = build_nets thms
	val tac = FCONV_TAC (MAIN_REWRITE_FCONV (cnet,fcnet))
   in
	TOP_DEPTH_CONV (FIRST_NET_CONV cnet tac)
   end;

(* rewrite a goal *)
val REWRITE_TAC = FCONV_TAC o rewrite_form;

(* rewrite a goal with help of its assumptions *)
fun ASM_REWRITE_TAC thl =
   ASSUM_LIST (fn asl => REWRITE_TAC (asl @ thl));

(* rewrite a theorem *)
val REWRITE_RULE = FCONV_RULE o rewrite_form;

(* rewrite a theorem with the help of iys assumptions *)
fun ASM_REWRITE_RULE thl th =
   REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;

(* reverse the direction of a term/formula rewrite *)
fun REV_REWRITE th0 =
   let
	val [th] = IMP_CANON th0
	val (_,conseq) = strip_imp (concl th)
   in
	if is_equiv conseq then ONCE_DEPTH_CHAIN SYM th
	else if is_iff conseq then ONCE_DEPTH_CHAIN FSYM th
	else raise rule with ("REV_REWRITE",[th0])
   end handle 
	general => raise rule with ("REV_REWRITE",[th0]) ||
	syntax => raise rule with ("REV_REWRITE",[th0]) ||
	rule   => raise rule with ("REV_REWRITE",[th0]) ;

(* return the arg if f accepts it, else pass on f's failure *)
fun good_arg f x = (f x;x);

(* return a pair of lists, all clauses used as term/formula rewrites
   - this should give the user some idea of what REWRITE_TAC is doing *)
fun used_rewrites thl =
   let val can_thl = flat (map IMP_CANON thl) 
   in 
	(mapfilter (good_arg IMP_REW_CONV2) can_thl,
	 mapfilter (good_arg IMP_REW_FCONV2) (mapfilter FCONV_CANON can_thl))
   end;

(* include the assumptions in the list of potential rewrites *)
fun asm_used_rewrites thl =
   ASSUM_LIST (fn asl => K (used_rewrites (asl @ thl)));
 
	
