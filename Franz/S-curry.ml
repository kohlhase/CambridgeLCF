(***************************************************************************
*
*	ml-curry
*
****************************************************************************
* Currying of Meta Language functions.
*)

(* functions on rhs found in L-list.l *)
fun mem x l = paired_mem(x,l);
fun exists p l = paired_exists(p,l);
fun forall p l = paired_forall(p,l);
fun find p l = paired_find(p,l);
fun tryfind f l = paired_tryfind(f,l);
fun filter p l = paired_filter (p,l);
fun mapfilter f l = paired_mapfilter(f,l);
fun rev_itlist f l x = paired_rev_itlist(f,l,x);

(**************************************************************************
* OBJ primitives 
* functions on rhs found in L-obj.l 
*)
fun set_left x y = paired_set_left(x,y);
fun set_right x y = paired_set_right (x,y);
fun eq x y = paired_eq(x,y);
fun cons x y = paired_cons(x,y);




