(* *********************************************************************
 *
 *	S-dml.ml
 *
 **********************************************************************
 * predefined functions 
 *)

fun null(nil)=true | null(l)=false;

local fun length1 (n, [ ])  = n   (*TAIL RECURSIVE*)
        | length1 (n, x::l) = length1 (n+1, l)   
in  fun length l = length1 (0,l) end;

fun hd(nil) = raise general with "hd"
  | hd (x::_) = x ;

fun tl (nil) = nil | tl(_::l) = l;

fun map (f) (nil) = nil |	
    map (f: 'a -> 'b) (x::l: 'a list) : 'b list = (f x)::(map f l);

fun size (str:string) : int = length (explode str);

fun ! (ref x) = x;

infix 3 o
fun (f o g) x = f(g(x));

fun fst (x,y) = x;
fun snd (x,y) = y;
