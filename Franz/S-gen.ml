(*******************************************************************************
*
*	GEN
*
********************************************************************************
* General purpose functions for sml
* Converted to Standard ML by P M Hedlund, Rutherford Appleton Lab. (1986)
*)


fun append l1 l2 = l1 @ l2;

(* use the character "sep" to split the string into non-empty words
   words2 "/" "abc//d/ef/" -> ["abc","d","ef"] *)
fun words2 sep str =
   let fun temp ch (chs,tokl) =
	if (ch:string) = sep then
	   if null chs then ([],tokl)
	   else ([],(implode chs)::tokl)
	else (ch::chs,tokl)
   in
	snd (itlist temp (sep::(explode str)) ([],[]))
   end;

(* words "are you there" -> ["are","you","there"] *)
val words = words2 " ";

fun maptok f str = map f (words str);

(*Short commands for loading files*)
fun loadt str = load (str,true) and loadf str = load (str,false);
val use = loadt;

fun compilet str = compile (str,true) and compilef str = compile (str,false);

(* concatination *)
fun concat str1 str2 = str1 ^ str2;

fun concatl strl = implode (itlist append (map explode strl) []);

fun message (str:string) = (print_string str;print_newline())

(* combinators *)
infix // ;
fun op // (f,g) (x,y) = (f x,g y);

(* composition for function that takes a paired argument *)
infix oo;
fun op oo (f,(g,h)) x = f(g x,h x);

fun I x = x;

fun K x y = x;

val KI = K I;

fun C f x y = f y x 	(* the permutator *)

fun W f x = f x x	(* the dublicator *)

fun B f g x = f (g x)	(* the compositor, curried form of "o" *)

(* S,K and l permit the definition of lambda abstraction
   fn x=>x = l actuallu unnecessary, since l = S K K
   fn x=>A = K A where A is a constant or a variable other than x
   fn x=>A B = S (fn x=>A) (fn x=>B)
*)

infix Co;
fun op Co (f,g) x y = f (g y) x; (* permutation composition *)

fun pair x y = (x,y);

fun curry f x y = f (x,y);

(* sequencing operators for functions *)
fun thenf (f,g) x = g (f x);
infix thenf;

fun orelsef (f,g) x = f x handle ? => g x;
infix orelsef;

fun all_fun x = x

fun no_fun x = raise general with "no_fun";

fun can f x = (f x;true) handle ? => false;

(* check that the value x satisfies the predicate p if so pass x on *)
fun assert p x = if p x then x else raise general with "assert";

fun syserror (str:string) =
  (print "LCF system error: ";print_string str;print_newline() ;
		raise general with "syserror");

fun funpow 0 _ x = x | funpow n f x = funpow (n-1) f (f x);
