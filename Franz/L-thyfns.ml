(******************************************************************************
*
*	THYFNS
*
******************************************************************************
* Original: F-thyfns (Cambridge LCF)
*)


fun new_axiom (name,fm) = new_open_axiom (name, gen_all fm);

(* declare an axiom, checking that it has no free variables. This catches
   spelling errors and undeclared constants *)
fun new_closed_axiom (axname,w) =
  if null (form_frees w) then
	new_open_axiom (axname,w)
   else
	raise theory with
		("new_closed_axiom: free variables in axiom: " ^ axname);

(* utilities for print theory *)
fun print_list incon (name:string) (prfn: 'a -> unit) l =
   if not (null l) then
 	(print_begin 2;
	 print_string name;
	 print_string " -- ";
	 print_break (2,0);
	 if incon then print_ibegin 0
	 else print_begin 0;
	 map (fn x=> (prfn x;print_break (5,0))) (rev l);
	 print_end();
	 print_end();
	 print_newline())
    else ();

(* print a token and type for constsnts, infixes and predicates *)
fun print_tok_ty (tok:string,ty) =
   (print_begin 2;
    print_string tok;
    print_break (1,0);
    print_type ty;
    print_end ());

(* print a labelled theorem or axiom *)
fun print_tok_thm (tok:string,th) =
   (print_begin 2;
    print_string tok;
    print_break (2,0);
    print_thm th;
    print_end());

(* create an example type using arguments of the form 'a, 'a'a, .. *)
fun apply_type_op (arity , name) =
(* could create a type variable 'a'a'a'a.... not so good! *)
   mk_type (name,map (mk_vartype o 
	(concat "'") o implode o (replicate "a")) (upto 1 arity));


fun print_theory (thy:string) =
   let
	val print_const = print_tok_ty o dest_const
   in
	(print_string ("Theory: " ^ thy);print_newline();
	print_list true "Parents" print_string (parents thy);
	print_list true "Types" (print_type o apply_type_op) (types thy);
	print_list true "Predicates" print_tok_ty (predicates thy);
	print_list true "Constants" print_const (constants thy);
	print_list true "Paired Infixes" print_const (paired_infixes thy);
	print_list true "Curried Infixes" print_const (curried_infixes thy);
	print_list false "Axioms" print_tok_thm (axioms thy);
	print_list false "Theorems" print_tok_thm (theorems thy);
	print_string "**************************************************************";
	print_newline())
   end;
	
