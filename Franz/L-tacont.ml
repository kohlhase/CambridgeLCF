(*******************************************************************************
*
*	TACONT
*
*******************************************************************************
* Original : tacont (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Theorem continuations.
*
* Many inference rules, particularly those involving disjunction and 
* existential quantifiers, produce inermediate results that are needed
* only briefly. One approach is to treat the assumtion list like a stack,
* pushing and popping theorems from it. However, it is traditional to regard
* the assumtions as unordered, also, stack operations are crude. 
*
* Instead, we adopt a continuation approach: a continuation is a function that
* maps theorems to tactics. It can put the theorem on the assumtion list,
* produce a case split, throw it away, etc. The text of a large theorem
* continuation should be a readable description of the flow of inference. *)

type thm_tactic = thm -> tactic;

type thm_tactical = thm_tactic -> thm_tactic;


fun THEN_TCL ((ttcl1:thm_tactical),(ttcl2:thm_tactical)) ttac =
   ttcl1 (ttcl2 ttac);
infix THEN_TCL;

fun ORELSE_TCL ((ttcl1:thm_tactical),(ttcl2:thm_tactical)) ttac th =
   (ttcl1 ttac th) handle 
	tactic => (ttcl2 ttac th) || syntax => (ttcl2 ttac th);
infix ORELSE_TCL;

fun REPEAT_TCL (ttcl:thm_tactical) ttac th =
   ((ttcl THEN_TCL (REPEAT_TCL ttcl)) ORELSE_TCL I) ttac th;

val ALL_THEN : thm_tactical = I;


val NO_THEN : thm_tactical = let fun temp ttac th = raise tactic with 
			("NO_THEN",[]) in temp end;

(* uses every theorem tactical *) 
(* EVER_TCL [ttcl1,...,ttcln] = ttcl1 THEN_TCL ... THEN_TCL ttcln; *)
fun EVERY_TCL ttcl1 = itlist (curry (op THEN_TCL)) ttcl1 ALL_THEN;

(* uses first successful theorem tactical 
   FIRST_TCL [ttcl1,...,ttcln] = ttcl1 ORELSE_TCL .... ORELSE_TCL ttcln *)
fun FIRST_TCL ttcl1 = itlist (curry (op ORELSE_TCL)) ttcl1 NO_THEN;

(* conjunction elimination 

	C
  ================	|- A1 /\ A2
	C
    ==========  ttac1 |- A1
      .......
    ==========  ttac2 |- A2
	...
*)
fun CONJUNCTS_THEN2 (ttac1:thm_tactic) ttac2 cth : tactic =
   let
	val (th1,th2) = CONJ_PAIR cth handle rule => 
			raise tactic with ("CONJUNCTS_THEN",[])
   in
	ttac1 th1 THEN ttac2 th2
   end;
   
(* disjunction elimination

		C
	====================	|-A1\/A2
	C		   C
      ======ttac1 A1|-A1 ======= ttac2 A2|^-A2
	..		   ..
*)
fun DISJ_CASES_THEN2 ttac1 ttac2 disth  : tactic =
   let
	val (a1,a2) = dest_disj (concl disth) handle syntax => 
		raise tactic with ("DISJ_CASES_THEN2",[])
   in
	fn (asl,w) =>
	   let
		val (gl1,prf1) = ttac1 (ASSUME a1) (asl,w)
	 	val (gl2,prf2) = ttac2 (ASSUME a2) (asl,w)
	   in
		(gl1@gl2,fn thl =>
		   let
			val (thl1,thl2) = chop_list (length gl1) thl
		   in
			DISJ_CASES disth (prf1 thl1) (prf2 thl2)
		   end)
	   end
   end;

(* single & multi-tactic versions *)
fun DISJ_CASES_THEN ttac =  DISJ_CASES_THEN2 ttac ttac;
val DISJ_CASES_THENL = end_itlist DISJ_CASES_THEN2;

(* implication introduction 

	A ==> B
   ================
	   B
   ================  ttac |-A
*)
fun DISCH_THEN ttac : tactic =
   fn ((asl,w):goal) =>
   let
	val (ante,conc) = dest_imp w handle syntax => 
		raise tactic with ("DISCH_THEN",[])
	val (gl,prf) = ttac (ASSUME ante) (asl,conc)
   in
	(gl,(DISCH ante) o prf)
   end;

(* iff elimination 

	C
 ================
	C
      =====ttac1 |-A!==>A2
	..
     =========ttac2|-A2==>A1
	..
*)
fun IFF_THEN2 (ttac1:thm_tactic) ttac2 iffth : tactic =
   let
	val (th1,th2) = CONJ_PAIR (IFF_CONJ iffth) handle rule => 
		raise tactic with ("IFF_THEN2",[])
   in
	ttac1 th1 THEN ttac2 th2
  end;

fun IFF_THEN ttac = IFF_THEN2 ttac ttac;

(* existential elimination

	B
  ==============  |- ?x.A(x)
	B	
  ============== ttac A(y)
  	..
*)
fun X_CHOOSE_THEN y ttac xth : tactic =
   let
	val (x,body) = dest_exists (concl xth) handle syntax => 
		raise tactic with ("X_CHOOSE_THEN",[])
   in
	fn (asl,w) =>
	   let
		val (g1,prf) = ttac (ASSUME (subst_form [(y,x)] body)) (asl,w)
	   in
		(g1,(CHOOSE (y,xth)) o prf)
	   end
  end;

(* chooses a variant for the user *)
fun CHOOSE_THEN ttac xth : tactic =
   let
	val (x,body) = dest_exists (concl xth) handle syntax => 
		raise tactic with ("CHOOSE_THEN",[])
   in
	fn (asl,w) =>
	   let
		val y = variant ((thm_frees xth)@(forml_frees (w::asl))) x
	   in
		X_CHOOSE_THEN y ttac xth (asl,w)
	   end
   end;

(* Cases tactics *)

(* for a generalized disjunction |-(?xl1.B1(x1l)) \/ .. \/ (?xln.Bn(xln))
  where the xl1 .. xln are the vectors of zero or morevariables in
  eachof yl1 .. yln have the same types as the corresponding xli do

			A
   ================================================
	A				A
   =========== ttac1 |-B1(yl1)	  ================= ttacn |-B(yln)
	..				..
*)
fun X_CASES_THENL varsl ttacl =
   DISJ_CASES_THENL
   	(map (fn (vars,ttac) => EVERY_TCL (map X_CHOOSE_THEN vars) ttac)
	   (varsl com ttacl));


fun X_CASES_THEN varsl ttac =
   DISJ_CASES_THENL
	(map (fn vars => EVERY_TCL (map X_CHOOSE_THEN vars) ttac) varsl);


(* version that chooses the y's as variants of the x's *)
fun CASES_THENL ttacl =
   DISJ_CASES_THENL (map (REPEAT_TCL CHOOSE_THEN) ttacl);

fun CONJUNCTS_THEN ttac = CONJUNCTS_THEN2 ttac ttac;

(* tactical to strip off one disjunction, conjunction or existential *)
val STRIP_THM_THEN =
   FIRST_TCL [CONJUNCTS_THEN,DISJ_CASES_THEN,CHOOSE_THEN];
