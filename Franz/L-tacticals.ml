(*****************************************************************************
*
*	TACTICALS
*
******************************************************************************
* Original: tacticals (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Monomorhic tacticals.
*)
type proof = thm list -> thm;

type goal = form list * form;

type tactic = goal -> ((goal list) * proof);

(* exception tactic must be declared in ML since the type goal is not
   declared in lisp but in ML *)
exception tactic: string * goal list;

(* TAC_PROOF (g,tac) uses tac to prove the goal g *)
fun TAC_PROOF  ((g,tac) : (goal * tactic)) : thm =
   let
	val (gl,p) = tac g 
   in
	if null gl then p[] else raise tactic with
		("TAC_PROOF: unsolved goals",[g])
  end;


(* provide a function with the current assumption list *)
fun ASSUM_LIST (aslfun:thm list -> goal -> 'a)  ((asl,w):goal) : 'a =
   aslfun (map ASSUME asl) (asl,w);

(* pop the first assumption and give it to a function 8tactic) *)
fun POP_ASSUM thfun (((as'::asl),w):goal) =
   thfun (ASSUME as') (asl,w) ;

(* pop off the entire assumption list and give it to a function (tactic) *)
fun POP_ASSUM_LIST asltac ((asl,w):goal) =
   asltac (map ASSUME asl) (([],w):goal);

fun mapshape [] fl l = [] | 
    mapshape (hnl::tnl) (hfl::tfl) l = 
      let val (m,l) = chop_list hnl l
      in
	hfl m :: mapshape tnl tfl l
      end;



fun THEN (tac1,tac2) g =
   let
	val (gl,p) = tac1 g
	val (gl1,p1) = split (map tac2 gl)
   in
	(flat gl1, (p o mapshape (map length gl1) p1))
   end;
infix THEN;


fun THENL (tac1,tac2l) g =
   let
	val (gl,p) = tac1 g
	val tac2gl = combine (tac2l,gl) handle general => raise tactic with
				("THENL ",[g])
	val (gl1,p1) = split (map (fn (tac2,g) => tac2 g) tac2gl)
   in
	(flat gl1,(p o mapshape (map length gl1) p1))
   end;
infix THENL;

(* syntax rule should not be here, but somehow a syntax exception slips through *)
fun ORELSE (tac1,tac2) g = (tac1 g) handle 
			syntax => (tac2 g) ||
			tactic => (tac2 g);
infix ORELSE;

(* fail with given string *)
fun FAIL_TAC (str:string) g = raise tactic with (("FAIL_TAC: " ^  str),[g]);

(* tactics that succeeds on no goals; identity for ORELSE *)
val NO_TAC  = FAIL_TAC "NO_TAC";

(* tactic that succeeds on all goals; identity for THEN *)
fun ALL_TAC g = ([g],hd);

fun TRY tac = tac ORELSE ALL_TAC;

(* the abstraction around g is essential to avoid looping, due to
   applicative order semantics *)
fun REPEAT tac g =
   ((tac THEN REPEAT tac) ORELSE ALL_TAC) g;

(* check whether a theorem achieves a goal, using no extra assumptions *)
fun achieves th =
   (fn (asl,w) => (aconv_form (concl th) w andalso
   forall (fn h => (exists (aconv_form h)) asl) (hyp th)));

(*
Make a theorem that assumes falsity
A legitimate way for the user to make a theorem of (almost) any form,
for testing of derived inference rules.  Most rules won't notice the extra
assumption, strong though it is.
Note: this function should belong in L-pcrule.ml
*)
fun mk_fthm (asl,w) = mk_thm(falsity::asl, w);

fun fakethms gl = map mk_fthm gl;

(*check the goal list and proof returned by a tactic. At top level it is
  convenient to type "chktac it;" *)
fun chktac (gl,prf) = prf (fakethms gl);

(* check whether a prospective (goal list,proof) pair is valid *)
val check_valid (* :  (goal list * proof) -> bool *) =
   fn (asl,w) => 
	let fun temp glp = achieves (chktac glp) (falsity::asl,w)
	in
	   temp
	end;

(* Tactcal to make any tactic valid. "VALID tac" is the same as tac except
   it will fail in the cases tac returns an invalid proof. This check 
   is accurate unless the the proof depends on the assignable variables or 
   notices  the extra hypothesis FALSITY. VALID uses mk_fthm (which assumes
   falsity) insted of mk_thm, for the proof could assign its arguments to global
   theorem variables, making them accessible outside. *)
fun VALID  tac g =
   let
	val (gl,prf) = tac g 
   in
	if check_valid g (gl,prf) then (gl,prf) else raise tactic with 
					("VALID",[g])
    end;


(* Tactical quantifiers, Apply a list of tactics in succession *)

(* uses every tactic 
   EVERY [TAC1,...,TACn] = TAC1 THEN ... THEN TACn *)
fun EVERY tacl = itlist (curry (op THEN)) tacl ALL_TAC;

(* uses first tactic that succeeds
   FIRST [TAC1,...,TACn] = TAC1 ORELSE ... TACn *)
fun FIRST tacl g = tryfind (fn tac => tac g) tacl handle 
	general => raise tactic with ("FIRST",[g]) ||
	tactic  => raise tactic with ("FIRST",[g]);

fun MAP_EVERY tacf lst = EVERY (map tacf lst) ;
fun MAP_FIRST tacf lst = FIRST (map tacf lst);

(* call a thm-tactic for every assumption *)

val EVERY_ASSUM = ASSUM_LIST o MAP_EVERY;

(* call a thm-tactic for the first assumption at which it succedds *)
val FIRST_ASSUM = ASSUM_LIST o MAP_FIRST;

(* Split off a new subgoal and provide it as a theorem to a tactic
	SUBGOAL_THEN wa (fn tha => tac)
   makes a subgoal of wa, and also assumes wa for proving the original goal.
   Most convinient when te tactic solves the original goal, leaving onle the
   new subgoal wa. *)
fun SUBGOAL_THEN wa (ttac) =
  fn (asl,w) =>
   let
	val (gl,p) = ttac (ASSUME wa) (asl,w)
     in
	(((asl,wa)::gl),(fn (tha::thl) => CUT tha (p thl)))
   end;

