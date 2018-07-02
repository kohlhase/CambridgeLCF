(***************************************************************************
*
*	STACK
*
***************************************************************************
* Original : stack (Cambridge LCF) 
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab.
*
* A system of routines to maintaingoals and partial results. You
* crate and traverse the proof tree top-down, left to right.
* You expand the current goal into a list of subgoals, which are
* pushed onto the goalstack, on top of the proof.
*
* Operations:
*	set_goal g 	state the top-level goals
*	expand tac	apply a tactic to top-most goal
*	expandf tac	fast expand
*	print_state n	print top-most n goals
*	top_thm         top of thmstack
*	save_top_thm i  call save_thm (i,top of thmstack)
*	rotate n	rotate goals to move the nth goal to the front
*	backup()	undo last proof step (may be repeated )
*)

abstype goalstack = rep_goalstack of subgoals list
with
   fun rep_goals (rep_goalstack l) = l
   fun abs_goals g = rep_goalstack g
end;

val goals = ref (abs_goals [])
and  (backup_list : goalstack list ref) = ref [];

(* parameters for the user to adjust *)

(*minimun number of previous states to retain *)
val back_up_limit = ref 12;

fun print_state depth =
   print_stack (rep_goals (!goals)) depth;

fun change_state newgoals =
   let
	val newbackup =
		fst (chop_list (!back_up_limit) (!backup_list))
		handle 
		   general => (!backup_list) ||
		   match => (!backup_list)
   in
	(backup_list := (!goals)::newbackup;
	 goals := newgoals)
   end;

(* set the top-level goal, initialize *)
fun set_goal g = change_state (abs_goals (new_stack g));

(*expand the top subgoal using the tactic *)
fun expandf tac =
	change_state (abs_goals (push_fsubgoals (rep_goals (!goals)) tac));

(* expand after validating tactic *)
val expand = expandf o VALID;

(* rotate goalseh of current proof *)
fun rotate n = change_state (abs_goals (rotate_top n (rep_goals (!goals))));

(* restore the previous proof state, discard current state *)
fun backup () : unit =
   let
	val (newgoals::newbackup) =  (!backup_list)
   in
	if null (rep_goals newgoals) then 
		raise general with "backup: no newgoals"
	else
	   (goals := newgoals;
	    backup_list := newbackup;
	    print_state 1;())
   end handle 
		bind => raise general with "backup_list is empty" ||
		match => raise general with "backup list is empty" ;


(* return top-most theorem *)
fun top_thm() = top_proof (rep_goals (!goals));

(* record top-most theorem on a Fact file *)
fun save_top_thm name = save_thm (name, top_thm());

fun top_goal () : goal =
   let
	val ((g::gl),prf) = hd (rep_goals (!goals))
   in
	g
   end;

val get_state : unit -> goalstack = fn () => (!goals)

fun set_state goals = (change_state goals;print_state 1);
