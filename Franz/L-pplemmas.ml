(*******************************************************************************
*
*	PPLEMMAS
*
********************************************************************************
* Original: pplemmas (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Basic pplambda lemmas and derived inference rules.
* The following non-logical inference rules can be derived from the axioms
* alone. Some have been coded using mk_thm for speed. 
*)
val CLOSE_UP = GEN_ALL o DISCH_ALL;


fun save_thm (name,th) =  save_open_thm (name,CLOSE_UP th);

(* !x. x==x *)
val EQ_REFL = 
   CLOSE_UP (let 
		val refl = SPEC `x: 'a ` LESS_REFL  
	    in
		MP (SPECL [`x: 'a `,`x: 'a `] LESS_ANTI_SYM) (CONJ refl refl)
	   end); 


(* !x y.x==y ==> x<<y  /\ y<<x *) 
val EQ_ANAL = 
   CLOSE_UP (let val eq = ASSUME `x==y : 'a ` val refl = SPEC `x: 'a ` LESS_REFL
	    in
		CONJ (SUBS_OCCS [([2],eq)] refl) (SUBS_OCCS [([1],eq)] refl)
	    end);

(* !x y. x==y ==> y==x *)
val EQ_SYM =
  CLOSE_UP
   (let
	val (xyth,yxth) = 
	  CONJ_PAIR(MP (SPECL [`x: 'a`,`y: 'a`] EQ_ANAL) (ASSUME `x==y: 'a`))
   in
	MP (SPECL [`y: 'a`,`x: 'a`] LESS_ANTI_SYM) (CONJ yxth xyth)
   end);



(* !x y z. x==y /\ y==z ==> x=z *)
val EQ_TRANS =
   CLOSE_UP (let
		val (xyeq,yzeq) = 
		  CONJ_PAIR (ASSUME `x==y: 'a /\ y==z: 'a `)
		val (xyless,yxless) =
		  CONJ_PAIR (MP (SPECL [`x: 'a `,`y: 'a `] EQ_ANAL) xyeq)
		val (yzless,zyless) =
		  CONJ_PAIR (MP (SPECL [`y: 'a `,`z: 'a `] EQ_ANAL) yzeq)
	  	val xzless =  MP(SPECL [`x: 'a `,`y: 'a `,`z: 'a `] LESS_TRANS)
				(CONJ xyless yzless)
		val zxless = MP (SPECL [`z: 'a `,`y: 'a `,`x: 'a `] LESS_TRANS)
				(CONJ zyless yxless)
	    in
		MP(SPECL [`x: 'a `,`z: 'a `] LESS_ANTI_SYM) (CONJ xzless zxless)
	   end);



(* !f g. (!x. f x==g x) ==> f==g  *)
val EQ_EXT =
   CLOSE_UP (let
		val f = `f: 'a -> 'b `
		val g = `g: 'a -> 'b `
		val x = `x: 'a `
		val (fgx_less,gfx_less) =
		   CONJ_PAIR
		     (MP (SPECL [`^f ^x`,`^g ^x`]
			(INST_TYPE [(`: 'b `, `: 'a `)] EQ_ANAL))
			(SPEC x (ASSUME `!^x. ^f ^x == ^g ^x`)))
		val fg_less = MP (SPECL [f,g] LESS_EXT) (GEN x fgx_less)
		val gf_less = MP (SPECL [g,f] LESS_EXT) (GEN x gfx_less)
	    in
		MP (SPECL [f,g] (INST_TYPE [(`: 'a -> 'b `,`: 'a `)] LESS_ANTI_SYM))
			(CONJ fg_less gf_less)
	   end);


(* `t` ->  |-`t==t` *)
fun REFL t = mk_thm ([], `^t==^t`);

		

(*	t==u
    -----------
	u==t
*)
fun SYM th =
   let
	val (hyps,conc) = dest_thm th
	val (x,y) = dest_equiv conc
   in
	mk_thm (hyps,mk_equiv (y,x))
   end handle syntax  => raise rule with ("SYM",[th]);

(*		x==y
	---------------------
	  x<<y  /\  y<<x
*)
fun ANAL eqth =
   let
	val (x,y) = dest_equiv (concl eqth)		
   in
	MP (SPECL [x,y] (INST_TYPE [(type_of x,`: 'a `)] EQ_ANAL)) eqth
   end handle 
	rule => raise rule with ("ANAL",[eqth]) ||
	syntax => raise rule with ("ANAL",[eqth]);


fun SYNTH conjth =
   let
	val (x,y) =dest_inequiv (fst (dest_conj (concl conjth)))
   in
	MP (SPEC y (SPEC x (INST_TYPE [(type_of x,`: 'a `)] LESS_ANTI_SYM)))
	conjth
   end handle 
		syntax => raise rule with ("SYNTH",[conjth]) ||
		rule => raise rule with ("SYNTH",[conjth]);

(*	t =< u	u=<v
   ---------------------
	  t =< v
*)
fun TRANS (th1,th2) =
   let
	val (sym1,arg1) =dest_pred (concl th1)
	val (sym2,arg2) = dest_pred (concl th2)
	val hyps = union (hyp th1) (hyp th2)  
	val (x,y) =  dest_pair arg1
	val (y',z) = dest_pair arg2
	val l = ["equiv","inequiv"]
   in
	if aconv_term y y' then
	  if sym1 = "equiv" andalso sym2 = "equiv" then
		mk_thm (hyps,`^x==^z`)
	   else if mem sym1 l andalso mem sym2 l then 
		mk_thm (hyps,`^x<<^z`)
	   else raise general with ""
	else raise general with ""
   end handle 
	general => raise rule with ("TRANS",[th1,th2]) ||
	syntax => raise rule with ("TRANS",[th1,th2]) ||
	rule => raise rule with ("TRANS",[th1,th2]);

infix TRANS;

(*	!x. u x=< v x
	---------------
	  u =< v
*)
fun EXT qth =
   let
	val (x,body) = dest_forall (concl qth)
	val (sym,arg) = dest_pred body
	val (ux,vx) = dest_pair arg
	val LE_EXT = if sym = "equiv" then EQ_EXT else LESS_EXT
   	val (u,_) = dest_comb ux
	val (v,_) = dest_comb vx
   in
	MP (SPECL [u,v]
	  (INST_TYPE [(type_of x,`: 'a `),(type_of ux, `: 'b `)] LE_EXT)) qth
   end handle 
	syntax => raise rule with ("EXT",[qth]) ||
	rule => raise rule with ("EXT",[qth]);


(*	|-`~TT == FF /\ ~FF == TT /\
	    ~ TT == UU /\ ~UU == TT /\
	    ~FF == UU /\ ~UU == FF `
*)
val TR_EQ_DISTINCT =
   CLOSE_UP (let
	val LESS_DIST_L = CONJUNCTS TR_LESS_DISTINCT
	fun MP_DIST ante =
	   DISCH_ALL (tryfind (fn imp => MP imp ante) LESS_DIST_L)
	fun prove_not (t,u) = 
	   [MP_DIST (CONJUNCT1 (ANAL (ASSUME `	^t==^u`))), 
	    MP_DIST (CONJUNCT2 (ANAL (ASSUME `^u==^t`)))]
   in
	LIST_CONJ
	  (flat (map prove_not 
	    [(`TT`,`FF`),(`TT`,`UU:tr`),(`FF`,`UU:tr`)]))
    end);


(* `t` -> |- `UU << t` *)
fun MIN t =
   SPEC t (INST_TYPE [(type_of t, `: 'a `)] MINIMAL);



(* |-!x: 'a. (UU: 'a -> 'b ) x == UU *)
val MIN_COMB =
   CLOSE_UP 
	(let
	   val x=`x: 'a `
	   val uuabs = `\^x.(UU: 'b )`
	   val uufun = `UU: 'a -> 'b `
	 in
	    (SYNTH
		(CONJ (SUBS [BETA_CONV `^uuabs ^x`]
		   (MP (SPECL [uufun,uuabs,x,x] MONO)
			(CONJ (MIN uuabs) (SPEC x LESS_REFL))))
			  (MIN `^uufun ^x`)))
	 end);

	 
(* |- \x.UU == UU *)
val MIN_ABS =
   CLOSE_UP
	(EXT (GEN `z: 'a ` (BETA_CONV `(\x: 'a.UU: 'b ) z` TRANS
	   (SYM (SPEC `z: 'a ` MIN_COMB)))));	

(* |- `!f. \x.f x ==f *)
val ETA_EQ =
   CLOSE_UP (EXT (GEN `y: 'a ` (BETA_CONV `(\x: 'a. (f: 'a -> 'b ) x) y`)));

(*	x<<UU
	-------
	x==UU
*)
fun LESS_UU_RULE lth =
   SYNTH (CONJ lth (MIN (lhs (concl lth)))) handle rule => 
		raise rule with ("LESS_UU_RULE",[lth]);
	
val LESS_UU =
   CLOSE_UP
       (CONJ_IFF (CONJ (DISCH `x<<UU: 'a ` (LESS_UU_RULE (ASSUME `x<<UU: 'a`)))
	  (DISCH `x==UU: 'a` (SUBST [(SYM (ASSUME `x==UU: 'a `),`x: 'a `)] `x<<UU: 'a `
	   	(SPEC `UU: 'a ` LESS_REFL)))));


(*	f==g
	x==y
	------
	f x == g y
*)
fun MK_COMB (funth,argth) =
    let 
	val (f,g) = dest_equiv (concl funth)
	val (x,y) = dest_equiv (concl argth)
   in
	mk_thm (union (hyp funth) (hyp argth), `^(mk_comb (f,x)) ==
						^(mk_comb (g,y))`)
   end handle syntax => raise rule with ("MK_COMB",[funth,argth]);


fun LESS_MK_COMB (funth,argth) = 
   let
	val (f,g) = dest_inequiv (concl funth)
	val (x,y) = dest_inequiv (concl argth)
	val (_,[ty1,ty2]) = dest_type (type_of f)
				(* bind could be raised here *)
  in
	MP (SPECL [f,g,x,y] (INST_TYPE [(ty1,`: 'a `),(ty2,`: 'b `)] MONO))
	   (CONJ funth argth)
   end handle 
	bind => raise rule with ("LESS_MK_COMB",[funth,argth]) ||
	syntax => raise rule with ("LESS_MK_COMB",[funth,argth]) ||
	rule => raise rule with ("LESS_MK_COMB",[funth,argth]);


(*	f <= g
	x <= y
	------
	f x <= g y
*)
fun LE_MK_COMB (funth,argth) =
   (if is_equiv (concl funth) andalso is_equiv (concl argth) then
	MK_COMB (funth,argth)
   else
	let
	   fun rule th = CONJUNCT1 (ANAL th) handle 
			syntax => th || rule => th
	in
	   LESS_MK_COMB (rule funth,rule argth)
	end)
   handle rule => raise rule with ("LE_MK_COMB",[funth,argth]);


(*	u=<v
   ------------
    t u =< t v
*)
fun AP_TERM t th =
   LE_MK_COMB (REFL t, th)  handle rule => raise rule with ("AP_TERM",[th]);


(*	u=<v
    -------------
   u t =< v t
*)
fun AP_THM th t =
  LE_MK_COMB (th,REFL t) handle rule => raise rule with ("AP_THM",[th]);


(*	!x. u =< v
   ---------------------
   \x.u =< \x.v
*)
fun MK_ABS qth =
   let
	val (x,body) = dest_forall (concl qth) 
	val (sym,arg) = dest_pred body
	val (lh,rh) = dest_pair arg
   in
	if sym = "equiv" orelse sym = "inequiv" then
	   mk_thm (hyp qth,mk_pred (sym, `(\^x.^lh),(\^x.^rh)`))
	else raise general with ""
   end handle 
	general => raise rule with ("MK_ABS",[qth]) ||
	syntax => raise rule with ("MK_ABS",[qth]);


(*	!x. u x =< t
   --------------------
	u =< \x.t
*)
fun HALF_MK_ABS qth =
  let
	val (x,body) = dest_forall (concl qth)
	val t= rhs body
	val gv = genvar (type_of x)
	val tfun = mk_abs (x,t)
   in
	EXT (GEN gv ((SPEC gv qth) TRANS (SYM (BETA_CONV (mk_comb (tfun,gv))))))
   end handle 
	syntax => raise rule with ("HALF_MK_ABS",[qth]) ||
	rule => raise rule with ("HALF_MK_ABS",[qth]);


(* rename the bound variable of a lambda construction *)
fun ALPHA_CONV x t =
   let
	val x' = variant (term_frees t) x
  in
	HALF_MK_ABS (GEN x' (BETA_CONV (mk_comb (t,x))))
   end handle rule => raise rule with ("ALPHA_CONV",[]);


val FST_STRICT =
   LESS_UU_RULE (AP_TERM `FST: ('a * 'b ) -> 'a ` (MIN `UU: 'a,UU: 'b `)
    TRANS  (SPECL [`UU: 'a `,`UU: 'b `] FST_PAIR));

val SND_STRICT =
   LESS_UU_RULE (AP_TERM `SND: ('a * 'b ) -> 'b `(MIN `UU: 'a, UU: 'b `)
     TRANS(SPECL [`UU: 'a `,`UU: 'b `] SND_PAIR));
