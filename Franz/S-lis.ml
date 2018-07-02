(***************************************************************************
*
*	L-lis
*
****************************************************************************
* Original: lis.ml (Cambridge LCF)
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
* List processing functions
*)

fun itlist f l x = paired_rev_itlist(f,rev l,x);

(* [x1, ... ,xn] -> (ff x1 ... (ff (xn-1) xn) ... ) for n>0 *)
fun end_itlist _ nil = raise general with "end_itlist" |
    end_itlist ff l = 
           let 
	      val (last::rest) = rev l
	   in
	      paired_rev_itlist (ff,rest,last)
	   end;

fun eqfst_int (x:int) (y,z) = (x=y)
and eqsnd_int (x:int) (y,z) = (x=z);

fun assoc_int x = find (eqfst_int x)
and rev_assoc_int x = find(eqsnd_int x);

fun intersect l1 l2 = filter (fn x => mem x l2) l1;
fun subtract l1 l2 = filter(fn x => not (mem x l2)) l1;
fun union l1 l2 =  l1 @ (subtract l2 l1);

(* make a list into a set, stripping out dublicate elements *)
fun make_set l = 
   let fun temp a s = if mem a s then s else a::s
   in
	itlist temp l []
   end;

fun split [] = ([],[]) |
    split l =
	   let 
		val ((x1,x2):: l') = l
	   in
  		let 
		   val (l1',l2') = split l'
		in
		   (x1::l1',x2::l2')
	 	end
	   end;

fun combine ([],[]) = [] |
    combine (i1::l1,i2::l2) = 
	((i1,i2)::(combine (l1,l2))) handle match => 
					raise general with "combine"
		
infix com;
val op com = combine; 

(* check if the elements of l are all distinct *)
fun distinct [] = true | 
    distinct (x::l) = (not (mem x l)) andalso distinct l;

(* chop list n [e1, ...,en,e[n+1], ... e[n+m] -> [e1,..,en],[e[n+1],..,e[n+m]]*)
fun chop_list 0 l = ([],l) |
    chop_list n (x::l) =
	let val (m,l') = chop_list (n-1) l
	in
	   (x::m,l') 
	end handle match => raise general with "chop_list";

fun rotate_left (x::l) = l@[x]
and rotate_right (l) =
	let val (x::l') = rev l
	in
	   x::(rev l')
	end;

(* [[1,2,3],[4,5,6],[7,8,9]] -> [1,5,9] *)
fun diagonal [] = [] |
    diagonal ((x1::l1)::l) = x1::(diagonal (map tl l));

(* [x1,..,x(m+n)] -> ([y1,..,ym],[z1,..,zn]) 
   where the y's are all x's that satisfy p,the z's are all other x's *)
fun partition p l = 
  let
	fun temp a (yes,no) = if p(a) then (a::yes,no) else (yes,a::no)
  in
	itlist temp l ([],[])
  end;

(* make the list [x,..,x] of length n *)
fun replicate x n =
   if n<0 then raise general with "replicate"
   else if n=0 then [] else x::(replicate x (n-1));


(* make the list [from,from+1, .. ,to] *)
fun upto from to =
   if from>to then [] else from::(upto (from+1) to);
