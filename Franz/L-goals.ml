(*************************************************************************
*
*		GOALS
*
**************************************************************************
* Original : goals (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. 
*
* Utilities for maintaining subproofs, underlies goalstack package 
*)

(* print as'sumptions - in reverse order *)
fun print_hyps asl =
   let
	fun print' as' =
	   (print_string "  [";print_form (as'); print_string "]";print_newline())
   in
	(map print' (rev asl);())
   end;

fun print_goal (asl,w) =
   (print_form w;print_newline();print_hyps asl;print_newline());

(* prove and store a theorem *)
fun prove_thm (str,w,(tac:tactic)) =
   let
	val (gl,prf) = tac ([],w)
   in
	if null gl then save_thm (str,prf[])
	else
	   (message "unsolved goals: ";
	    map print_goal gl;
	    print_newline();
	    raise tactic with 
		("prove_thm: could not prove " ^ str, [ ([],w)]))
   end;

type subgoals = goal list * proof;

(* the key to handling subgoals is to incorporate proved ones into the
   proof immediately - suppose a tactic returns 3 subgoals:
	([g2,g3],prf3)
   after proving a theorem th1 that achieves gl, we get the subgoals
	([g2,g3],prf2)	where prf2 [th2,th3] = prf3 [th1,th2,th3]
   rotating the subgoals gives:
	([g3,g2],prf2')	where prf2' [th3,th2] = prf2 [th2,th3]
*)
fun root_goal g :subgoals = ([g],fn [th] => th);

fun attempt_first ((gl,pr):subgoals) tac : subgoals =
   if null gl then 
	raise general with "attempt_first: no goals to expand"
   else tac (hd gl);

fun rotate_goals (gl,pr) : subgoals =
   (rotate_left gl,pr o rotate_right) handle 
		match => raise general with "rotate_goals" ||
		general => raise general with "rotate_goals";


fun achieve_first (((asl,w)::gl),pr) th : subgoals =
   (gl,fn thl => pr (th::thl));


val apply_proof  = fn (([],pr):subgoals) => pr [];


fun print_subgoals ((gl,pr) : subgoals) =
   let
	val ngs = length gl
   in
	((if ngs > 1 then
	   (print_int ngs;print_string " subgoals"; print_newline())
	else if ngs = 0 then
	   (print_string "goal proved"; print_newline())
	else (print_string "1 subgoal"; print_newline());
        map print_goal (rev gl));())
   end;

fun print_stack sg_stack n =
   let
	val stackl = fst (chop_list n sg_stack) handle 
			match => sg_stack ||
			general => sg_stack 
   in
	(map print_subgoals (rev stackl);())
   end;

(* use complete proofs to satisfy goals *)
fun pop_proofs sg_stack =
   let
	val (sgs1::sgs2::sg_tail) = sg_stack 
		(* exception match raised when no match *)
	val th = apply_proof sgs1
   in
	(print_thm th;print_newline();
	 pop_proofs (achieve_first sgs2 th::sg_tail)) 
   end handle match => sg_stack || bind => sg_stack;

(* pop proofs and print new stack if different *)
fun pop_proofs_print sg_stack =
   let
	val sg2 = pop_proofs sg_stack
   in
	(if (length sg2 < length sg_stack ) andalso not (null sg2) then
	   (print_newline();print_string "previous subproof: ";
	    print_newline();print_stack sg2 1) else (); sg2)
   end;

(* print a new layer of subgoals, and push it onto the stack*)
fun push_print sgs sg_stack =
   (print_subgoals sgs;sgs::sg_stack);

(* expand the top subgoal using the tactic, push and print new subgoals*)
fun push_fsubgoals sg_stack tac =
  if null sg_stack then 
     raise general with "push_fsubgoals: goal stack is empty"
  else
    pop_proofs_print (push_print (attempt_first (hd sg_stack) tac) sg_stack);

(* push subgoals after validating the tactic *)
fun push_subgoals sg_stack = (push_fsubgoals sg_stack) o VALID;

(* rotate subgoals on stack top *)
fun rotate_top n (sgs::sg_stack) =
   push_print (funpow n rotate_goals sgs) sg_stack;

(* create a new goalstack, containing the initial goals *)
fun new_stack g = push_print (root_goal g) [];

(* extract proof on the top of the stack *)
(* changed 18/5/87 *)
fun top_proof (sgs::sg_stack) = apply_proof sgs
        handle match => raise general with "top_proof: unsolved goals"
  | top_proof [] = raise general with "top_proof: goal stack is empty";



	   
