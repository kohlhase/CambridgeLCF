(*******************************************************************************
*
*	DRUL
*
*******************************************************************************
* Original: drul (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Useful derived inference rules 
*)

(* Generalise a theorem aver all variables free in conclusion but not in hyps
	A(x1,...,xn)
	------------------
	!x1 ..xn.A(x1,..xn)
*)
fun  GEN_ALL th =
   itlist GEN (subtract (form_frees (concl th)) (forml_frees (hyp th))) th;


(* discharge all hypothees
	[A1, ...,An] B
	-----------------
	A1 ==> ... ==> An ==> B *)
fun DISCH_ALL th = DISCH_ALL (DISCH (hd (hyp th)) th) handle 
				syntax => th ||
				general=> th ||
				rule   => th;

(*	!x1 ... xn. A(xi)
	-------------------- SPECL [t1,...,tn]
	     A(ti)
*)
val SPECL = rev_itlist SPEC;

(*	A ==> B
	-----------
	  [A] B
*)
fun UNDISCH th = MP th (ASSUME (fst (dest_imp (concl th))));

(* |- !x. A -> (x', |-A[x'/x] *)
fun SPEC_VAR th =
   let
	val (bv,_) = dest_forall (concl th)
	val bv' = variant (forml_frees (hyp th)) bv
   in
	(bv',SPEC bv' th)
   end;

(*	A1 ==> ... ==> An ==|> B
	-------------------------
	   [A1,...,An] B
*)
fun UNDISCH_ALL th =
   if is_imp (concl th)  then UNDISCH_ALL (UNDISCH th) else th;

(*	!x1 ... xn. A[xi]
	----------------
	   A[xi'/xi]
*)
fun SPEC_ALL th =
  let val (vars,_) = strip_forall (concl th) 
  in SPECL (map (variant (forml_frees (hyp th))) vars) th end;

(* use the conclusion of ath to delete a hypotheses of bth 
	A    [A] B
	----------
	    B

*)
fun CUT ath bth = MP (DISCH (concl ath) bth) ath;

(* |- A/\B 0> (|-A,|-B) *)
fun CONJ_PAIR th = (CONJUNCT1 th,CONJUNCT2 th)

(* [`|- A1`,...,`|-An`] -> `|-A1 /\ ... /\ An` where n>0 *)
val LIST_CONJ = end_itlist CONJ;

(* |-A1 /\ (...(... /\ An)...) -> [`|-A1`,...,`|-An`] where n>0 .
   n must be specified since An could itself be a conjunction *)

fun CONJ_LIST n th =
   (if n=1 then [th] else (CONJUNCT1 th::(CONJ_LIST (n-1) (CONJUNCT2 th))))
   handle rule => raise rule with ("CONJ_LIST",[th]);


(* `|-A1 /\ ... /\ An` -> [`|A1`, ... ,`|-An`] where n>0 *)
fun CONJUNCTS th =
   (CONJUNCTS (CONJUNCT1 th)@CONJUNCTS (CONJUNCT2 th)) 
   handle rule => [th] || syntax => [th];

(* `|- !x. (A1 /\ ...) /\ ... (!y. ... /\ An)` -> [`|-A1`,...,`|-An] *)
fun BODY_CONJUNCTS th =
  if is_forall (concl th) then BODY_CONJUNCTS (SPEC_ALL th) else
  if is_conj (concl th) then 
     BODY_CONJUNCTS (CONJUNCT1 th) @ BODY_CONJUNCTS (CONJUNCT2 th)
   else [th];

(* put a theorem : 
	|- !x. A1 ==> !y.A2 ==> ... ==> Am ==> B
   into cononical form
	strip out quantifiers,split conjunctions part
   A /\ B -> (A,B)
   (A/\B) ==> C -> A==> (B==>C)
   (A\/B) ==> C -> (A==>C,B==>C)
   (?x.A) ==> B -> A[x'/x] ==> B
   !x.A -> A[x'/x]
*)
fun IMP_CANON th =
   let 
	val w = concl th
   in
	if 
	   is_conj w then IMP_CANON (CONJUNCT1 th) @ IMP_CANON (CONJUNCT2 th)
	else
	   if is_imp w then
		let
		   val (ante,conc) = dest_imp w 
		in
		   if is_conj ante then
			let
			   val (a,b) = dest_conj ante
			in
			   IMP_CANON
			(DISCH a (DISCH b (MP th (CONJ (ASSUME a) (ASSUME b)))))
			end
		   else if is_disj ante then
			let
			   val (a,b) = dest_disj ante
			in
			   IMP_CANON (DISCH a (MP th (DISJ1 (ASSUME a) b))) @
			   IMP_CANON (DISCH b (MP th (DISJ2 a (ASSUME b))))
			end
		   else if is_exists ante then
			let
			   val (x,body) = dest_exists ante
			   val x' = variant (thm_frees th) x 
			   val 	body' = subst_form [(x',x)] body
			in
			   IMP_CANON
		     (DISCH body' (MP th (EXISTS (ante,x') (ASSUME body')))) 
			end
		   else map (DISCH ante) (IMP_CANON (UNDISCH th))
	        end
	else if is_forall w then IMP_CANON (SPEC_ALL th)
	else [th]
   end;


(*      A1 ... An
      A1 ==> ... => An ==> B
    ----------------------------
		B
*)
val LIST_MP = let fun temp x y = MP y x in rev_itlist temp end;

(*	A ==> B
	---------
	~B ==> ~A
*)
fun CONTRAPOS impth =
   let
	val (a,b) = dest_imp (concl impth)
	val notb = `~ ^b`
   in
	DISCH notb (DISCH a (MP (ASSUME notb) (MP impth (ASSUME a))))
   end;


(*	A \/ B
	--------
	~A ==> B
*)
fun DISJ_IMP dth =
   let
	val (a,b) = dest_disj (concl dth)
	val nota = `~ ^a`
   in
	DISCH nota
	   (DISJ_CASES dth 
		(CONTR b (MP (ASSUME nota) (ASSUME a)))
		(ASSUME b))
  end handle 
	syntax => raise rule with ("DISJ_IMP",[dth]) ||
	rule => raise rule with ("DISJ_IMP",[dth]);
	
(*	A\/B	[A] C 	[B] D
	----------------------
		C \/ D
*) 
fun DISJ_CASES_UNION dth ath bth =
   DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth);

(* forward chain using an inference rule on top-level sub parts of a
  theorem, could be extended to handle other connectives *)
fun SUB_CHAIN rule th  =
   let
	val w = concl th
   in
	if is_conj w then
	   CONJ (rule (CONJUNCT1 th))(rule (CONJUNCT2 th))
 	else if is_disj w then
	   let 
		val (a,b) = dest_disj w
	   in
		DISJ_CASES_UNION th (rule (ASSUME a)) (rule (ASSUME b))
	   end
	else if is_imp w then
	   let
		val (a,b) = dest_imp w
	   in
		DISCH a (rule (UNDISCH th))
	   end
	else if is_forall w then
	   let
		val (x',sth) = SPEC_VAR th
	   in
		GEN x' (rule sth)
	   end
	else th
   end;

(* repeatedly apply the rule *)
fun REDEPTH_CHAIN rule x =
   (SUB_CHAIN (REDEPTH_CHAIN rule) thenf
	((rule thenf (REDEPTH_CHAIN rule)) orelsef I))	x;

(* apply the rule no more than once in any one place *)
fun ONCE_DEPTH_CHAIN rule x =
  (rule orelsef SUB_CHAIN (ONCE_DEPTH_CHAIN rule)) x;

(* "depth SPEC" : specialize a theorem whose quantifiers are buried inside*)

fun DSPEC x = ONCE_DEPTH_CHAIN (SPEC x);
val DSPECL = rev_itlist DSPEC;

(* 	B
      -------
	[A] B
*)
fun ADD_ASSUM aw bth = UNDISCH (DISCH aw bth);


			


