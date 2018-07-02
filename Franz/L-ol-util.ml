(******************************************************************************
*
*	OL-UTIL
*
*******************************************************************************
* Object language utilities.
* Original: ol-util (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
*)

(* ([x1, .. ,xn],t) -> \x1 ... xn.t *)
fun list_mk_abs (vars,t) = itlist (curry mk_abs) vars t;

(* (oper,[arg1, ... ,argn] )-> oper arg1 .. argn *)
fun list_mk_comb (oper,args) =
   let fun temp x f = mk_comb(f,x)
   in
   	rev_itlist temp args oper
   end; (* let *)

(* ["A1", ... ,"An"] -> "A1 /\ ... /\ An", where n>0 *)
fun list_mk_conj [A] = A
  | list_mk_conj (A::AS) = mk_conj(A, list_mk_conj AS)
  | list_mk_conj [] = raise syntax with "list_mk_conj";

fun list_mk_disj [A] = A
  | list_mk_disj (A::AS) = mk_disj(A, list_mk_disj AS)
  | list_mk_disj [] = raise syntax with "list_mk_disj";

(* ([A1, ... ,An],B) -> A1 ==> ( ... (An ==> B) ... ) *)
fun list_mk_imp (antel,conc) = itlist (curry mk_imp) antel conc;

(* ([x1, ... ,xn],A) -> !x1 ... xn.A *)
fun list_mk_forall (vars,body) = itlist (curry mk_forall) vars body;

fun list_mk_exists (vars,body) = itlist (curry mk_exists) vars body;

fun strip_abs tm = 
	if is_abs tm then
	   let 
		val (bv,t) = dest_abs tm 
		val (bvs,core) = strip_abs t 
	   in
		(bv::bvs,core)
	   end
	else
	   ([],tm)
;

(* t u1 .. un -> (t,[u1, ... ,un] *)
fun strip_comb tm =
   let
	fun dest t rands =
	   if is_comb t  then
		let
		   val (rator,rand) = dest_comb t
		in
		   dest rator (rand::rands)
		end (* let *)	
	   else
		(t,rands)
   in
	dest tm []
   end; (* strip_comb *)

(* "A1 /\ ... /\ An"  -> [A1, ... ,An] *)
fun conjuncts w = 
   (let val (a,b) = dest_conj w in conjuncts a @ conjuncts b end)
   handle syntax => [w];

(* "A1 \/ ... \/ An" -> [A1, ... ,An] *)
fun disjuncts w = 
   (let val (a,b) = dest_disj w in disjuncts a @ disjuncts b end)
   handle syntax => [w];

(* Because conjuncts splits both the left and the rigth sides of conjunction,
   it does no commute with list_mk_conj. It may be useful to introduce
   list_dest_conj, for splitting only the right tails of conjunction.
   likewise for disjunction *)

(* "A1 ==> ... ==> An ==> B" -> ([A1, ... ,An],B) *)
fun strip_imp fm =
   if is_imp fm then
	let
	   val (wa,wc) = dest_imp fm
	   val (was,wb) = strip_imp wc
	in
	   (wa::was,wb)
	end
   else
	   ([],fm)
(* end strip_imp *);

(* !x1 ... xn.A -> ([x1, ..., xn],A) *)
fun strip_forall fm =
   (let 
	val (bv,body) = dest_forall fm
	val (bvs,core) = strip_forall body
   in
	(bv::bvs,core)
   end)
   handle syntax => ([],fm)
(* end strip_forall *);

(* ?x1 ... xn. A -> ([x1, ... , xn],A) *)
fun strip_exists fm =
   (let 
	val (bv,body) = dest_exists fm
	val (bvs,core) = strip_exists body
   in
	(bv::bvs,core)
   end)
   handle syntax => ([],fm)
(* end strip_exists *);

fun mk_pair (t,u) = `^t, ^u`;

fun mk_cond (p,t,u) = 
    `^p => ^t | ^u`  handle syntax => raise syntax with "mk_cond";

fun mk_equiv (t,u) = `^t == ^u`;

fun mk_inequiv (t,u) = `^t << ^u`;

fun is_pair tm =
   "PAIR" = fst(dest_const (fst (dest_comb (fst (dest_comb tm)))))
   handle syntax => false;

fun is_cond tm =
   "COND" = fst (dest_const (fst (dest_comb (fst (dest_comb (fst (dest_comb tm)))))))
   handle syntax => false;

fun is_equiv fm = 
  is_pred fm andalso fst(dest_pred fm) = "equiv";

fun is_inequiv fm =
   is_pred fm andalso fst(dest_pred fm) =  "inequiv";

(* `(x,y)` -> (`x`,`y`) *)
fun dest_pair tm =
   let
	val (rat,rand) = dest_comb tm
	val (ratrat,ratrand) = dest_comb rat
   in
	if fst (dest_const ratrat) = "PAIR" then 
	   (ratrand,rand)
	else
	   raise general with ""
   end
   handle 
	general => raise syntax with "dest_pair" ||
	syntax => raise syntax with "dest_pair";

(* p => x^y -> (p,x,y) *)
fun dest_cond tm =
   let
	val (cst,[p,x,y]) = strip_comb tm
   in
	if fst (dest_const cst) = "COND" then
	   (p,x,y)
	else
	   raise general with ""
   end
   handle 
	bind => raise syntax with "dest_cond" ||
	general => raise syntax with "dest_cond" ||
	syntax => raise syntax with "dest_cond";

(* x==y -> (x,y) *)
fun dest_equiv fm =
   let 
	val (sym,arg) = dest_pred fm
   in
	if sym = "equiv" then
	   dest_pair arg
	else
	   raise general with ""
   end
   handle 
	general => raise syntax with "dest_equiv" ||
	syntax => raise syntax with "dest_equiv";

(*  x << y -> (x,y) *)
fun dest_inequiv fm =
   let
	val (sym,arg) = dest_pred fm
   in
	if sym = "inequiv" then 
	   dest_pair arg
	else
	   raise syntax with "dest_inequiv"
   end;

fun gen_all fm =
   list_mk_forall (form_frees fm,fm);

(* these now work on all binary predicates *)
fun lhs fm = fst (dest_pair (snd (dest_pred fm))) handle syntax => 
			raise syntax with "lhs";

fun rhs fm = snd (dest_pair (snd (dest_pred fm))) handle syntax => 
			raise syntax with "rhs";

(* search a term for a sub term satisfying p *)
fun find_term_in_term p =
   let
	fun find_tm tm =
	   if p tm then tm
	   else if is_abs tm then find_tm (snd (dest_abs tm))
	   else if is_comb tm then
	     let
		val (rator,rand) = dest_comb tm
	     in
		find_tm rator handle 
				syntax => find_tm rand ||
				general => find_tm rand
	     end (* let *)
	   else raise general with "find_term_in_term"
   in
	find_tm
   end;


(* search a formula for a sub term satisfying p *)
fun find_term_in_form p =
  let
    fun find_tm fm =
	if is_forall fm then find_tm (snd (dest_forall fm))
	else if is_exists fm then find_tm (snd (dest_exists fm))
	else if is_conj fm then
	   let
		val (left,right) = dest_conj fm
	   in
		find_tm left handle 
			syntax => find_tm right ||
			general=> find_tm right
	   end
	else if is_disj fm then
	   let
		val (left,right) = dest_disj fm
	   in
		find_tm left handle 
			syntax => find_tm right ||
			general=> find_tm right
	   end
	else if is_imp fm then
	   let
		val (left,right) = dest_imp fm
	   in
		find_tm left handle 
			syntax => find_tm right ||
			general=> find_tm right
	   end
	else if is_iff fm then
	   let
		val (left,right) = dest_iff fm
	   in
		find_tm left handle 
			syntax => find_tm right ||
			general=> find_tm right
	  end
	else find_term_in_term p (snd (dest_pred fm))
   in
	find_tm
   end;
