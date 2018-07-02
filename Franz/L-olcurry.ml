(***************************************************************************
*
*	L-OL-CURRY
*
*****************************************************************************
* Original ol-curry (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* Currying of Object Language functions
*)

(* functions from L-thyfns *)
fun axiom thy factname = paired_axiom (thy,factname)
and theorem thy factname = paired_theorem(thy,factname)
and new_type arity tok = paired_new_type(arity,tok)
and delete_thm thy factname = paired_delete_thm (thy,factname);

(* functions from L-subst *)
fun aconv_term t u = paired_aconv_term (t,u)
and aconv_form w v = paired_aconv_form(w,v)
and subst_term l t = paired_subst_term(l,t)
and subst_form l f = paired_subst_form(l,f)
and subst_occs_term nl l t = paired_subst_occs_term (nl,l,t)
and subst_occs_form nl l f = paired_subst_occs_form (nl,l,f)
and term_freein_term l t = paired_term_freein_term(l,t)
and term_freein_form l f = paired_term_freein_form(l,f)
and form_freein_form l f = paired_form_freein_form(l,f)
and variant vl v = paired_variant(vl,v);

(* functions from L-inst *)
fun type_in_type ty1 ty2 = paired_type_in_type(ty1,ty2)
and type_in_term ty t = paired_type_in_term(ty,t)
and type_in_form ty f = paired_type_in_form (ty,f)
and inst_type l ty = paired_inst_type(l,ty)
and inst_term tml l tm = paired_inst_term (tml,l,tm)
and inst_form tml l fm = paired_inst_form (tml,l,fm);

(* functions from L-simpl *)
fun term_match pat ob = paired_term_match(pat,ob)
and form_match pat ob = paired_form_match (pat,ob);



