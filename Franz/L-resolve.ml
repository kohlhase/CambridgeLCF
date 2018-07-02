(*****************************************************************************
*
*		RESOLVE
*
******************************************************************************
* Original : resolve (Cambridge LCF) 
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab.,
*
* Resolution inference rules and tactics
*)

(* search among a list of implications to perform Modus Ponens *)
fun MULTI_MP impl ante = 
   tryfind (fn imp => MATCH_MP imp ante) impl handle 
	general => raise rule with ("MULTI_MP",[ante])  ||
	rule => raise rule with ("MULTI_MP",[ante]);

(* forwards chaining by Modus Ponens *)
val MP_CHAIN = REDEPTH_CHAIN o MULTI_MP;

(* accept a theorem that, properly instantiated, satisfies the goals *)
fun MATCH_ACCEPT_TAC th0 : tactic =
   let
	val fmatch = PART_FMATCH I th0 
	fun atac (asl,w) = ([],K (fmatch w))
   in
	(REPEAT GEN_TAC) THEN atac
   end;


(*One step of backwards chaining;  makes MATCH_ACCEPT_TAC obsolete
  From the theorem !x y...A1==>...==>An==>B derives the rule 
    A1'  ...  An'
    -------------
          B'           *)
fun IMP_CHAIN_TAC impth (asl,fm) =
    let val impth' = PART_FMATCH (snd o strip_imp) impth fm;    
        val (As,_) = strip_imp (concl impth')
    in  (map (fn fm => (asl,fm)) As,
         fn ths=> LIST_MP ths impth')  
    end
    handle general => raise tactic with ("IMP_CHAIN_TAC", [(asl,fm)]);


(* basic unit for resolution tactics *)
fun MATCH_MP_TAC impth =
   STRIP_THM_TAC o (MATCH_MP impth);

(* resolve implicative assumptions with an antecedent *)
fun ANTE_RES_THEN ttac ante : tactic =
   ASSUM_LIST (EVERY o (mapfilter (fn imp => ttac (MATCH_MP imp ante))));

(* repeatedly resolve an implication *)
fun RESOLVE_THEN antel ttac impth : tactic =
   let
	val answers = mapfilter (MATCH_MP impth) antel
   in
	EVERY (mapfilter ttac answers) THEN
	(EVERY (mapfilter (RESOLVE_THEN antel ttac) answers))
   end;

(* resolve all assuptions against an implication *)
fun IMP_RES_THEN ttac impth =
   ASSUM_LIST
	(fn asl => EVERY (mapfilter (RESOLVE_THEN asl ttac) (IMP_CANON impth)));	

(* resolve all implicative assumptions against the rest *)
fun RES_THEN ttac =
   ASSUM_LIST (EVERY o (mapfilter (IMP_RES_THEN ttac)));

(* a trick tactic for solving existential/disjunctive goals *)
fun SELF_RES_TAC (asl,w) = 
   IMP_RES_THEN ACCEPT_TAC
	(DISCH w (itlist ADD_ASSUM asl (ASSUME w))) (asl,w);

val IMP_RES_TAC = IMP_RES_THEN STRIP_THM_TAC;

val RES_TAC = RES_THEN STRIP_THM_TAC;

