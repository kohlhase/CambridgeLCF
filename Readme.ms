.NH
Introduction
.LP
Welcome to Cambridge LCF Version 1.5, in Standard ML!
.LP
Standard ML is the new meta language in this Cambridge LCF system.
The LCF part is basically the same as in the old
ML/LCF system; names of functions, tactics etc, remain basically the same.
However, some changes have been made that the user will notice:
.in +0.5i
.LP
.IP *) 
 The syntax of PPLAMBDA has changed to make it more consistent with 
Standard ML.
.IP **) 
The system takes advantage of the exception facility of Standard ML.
.IP ***)
 LCF has been extended by some new tactics.
.in -0.5i
.LP
Since Input/Output and Modules are not necessary
for LCF, these have not been implemented in this version. However,
the Core Language and the run-time support have been fully implemented.
.LP
The new LCF system has largely been based on the implementation
of the old ML/LCF system.
ML sources for LCF have been transliterated to ML and Lisp sources
rewritten to suit ML representations of data objects and exceptions.
.LP
For an introduction to Standard ML it is recommended to
read \fIFunctional Programming using Standard ML\fR by A Wikstrom
(Prentice Hall, 1987)
and for an introduction
to LCF \fILogic and Computation\fR by Lawrence Paulson
(Cambridge University Press, 1987).
.LP
It is required that a version of Franz Lisp is available under the name 
\fIlisp\fR on the host machine. The system was developed under the version
Opus 38.79 of Franz Lisp and is currently available on VAX, SUN, and Pyramid
machines. 
.LP
In Version 1.5, several serious bugs have been fixed,
SUN compatibility has been acheived, new examples have been added,
and the Help system has been installed.
.LP
.NH 
Standard ML
.LP
Standard ML can be built as a separate image but is also available
in LCF. The full core language has been implemented, but
note that a test for an exhaustive match is not made in this version.
Hence, the exception \fImatch\fR will be raised without any warning given
by the compiler should the match be non-exhaustive.
.LP
The latest changes to the syntax of ML 
(new datatype bindings, polymorhic references etc.) have not been incorporated 
but will be in later version.
.LP
The built-in functions and constants described in the next section
are available.
.LP
.NH 2
Built-in Functions and Constants \(dd
.FS
\(dd \fInum \fRstands for: \fIreal \fRor \fIint, nums \fRstands for 
\fIint, string \fRor
\fIstring, mty \fRstands for monotype and \fIety \fRstands for type admitting
equality.
.FE
.in +0.5i
.LP
\fBnil : \fI'a list
.LP
\fBmap : \fI('a \(-> 'b) -> 'a list -> 'b list
.LP
\fBrev : \fI'a list \(-> 'a list
.LP
\fBtrue,false : \fIbool
.LP
\fBnot : \fIbool \(-> bool
.LP
\fB~ : \fInum \(-> num 
.LP
\fBabs : \fInum \(-> num
.LP
\fBfloor : \fIreal \(-> int
.LP
\fBsqrt : \fIreal \(-> real
.LP
\fBsin,cos,arctan : \fIreal \(-> real	
.LP
\fBexp,ln : \fIreal \(-> real
.LP
\fBsize : \fIstring \(-> int
.LP
\fBchr : \fIint \(-> string
.LP
\fBord : \fIstring \(-> int
.LP
\fBexplode : \fIstring \(-> string list
.LP
\fBimplode : \fIstring list \(-> string
.LP
\fBref : \fI'a \(-> 'a ref \fR(Note: check for monotype made by typechecker)
.LP
\fB! : \fI'a ref \(-> 'a \fR(Note: contents of reference)
.LP
\fBprint : \fIty \(-> ty \fR(Note: accepts user defined datatypes)
.LP
\fBmakestring : \fIty \(-> string \fR(Note: accepts user defined datatypes)
.LP
\fBload : \fI(string * bool)  \(-> unit	\fR(Note: loads a file)
.LP
\fBcompile : \fI(string * bool) \(-> unit \fR(Note: compiles a file)
.LP
\fBsys : \fIstring \(-> unit \fR(Note: system call, eg. sys "cat file.ml";)
.LP
\fBsave : \fIstring \(-> unit \fR(Note: save the current state)
.in -0.5i
.LP
.NH 2
Operators with precedence:
.LP
.NH 3
Precedence 7
.LP
.in +0.5i
\fB/ : \fIreal * real \(-> real
.LP
\fBdiv : \fRint * int \(-> int
.LP
\fBmod : \fIint * int \(-> int
.LP
\fB* : \fInum * num \(-> num \(dd
.LP
.in -0.5i
.FS
\(dd Note that types of arguments to overloaded functions must be 
known at compile-time.
.FE
.LP
.NH 3	
Precedence 6
.in +0.5i
\fB+ : \fInum * num \(-> num
.LP
\fB- : \fInum * num \(-> num
.LP
\fB^ : \fIstring * string \(-> string
.LP
.in -0.5i
.LP
.NH 3
Precedence 5
.in +0.5i
\fB:: : \fI'a * 'a list \(-> 'a list
.LP
\fB@ : \fI'a list * 'a list \(-> 'a list
.LP
.in -0.5i
.LP
.NH 3
Precedence 4
.in +0.5i
\fB= : \fIety * ety \(-> bool
.LP
\fB<> : \fIety * ety \(-> bool
.LP
\fB< : \fInums * nums \(-> bool
.LP
\fB> : \fInums * nums \(-> bool
.LP
\fB<= : \fInums * nums \(-> bool
.LP
\fB>= : \fInums * nums \(-> bool
.LP
.in -0.5i
.NH 3
.in +0.5i
Precedence 3
.LP
\fBo : \fI('b \(-> 'c) * ('a -> 'b) -> ('a -> 'c)
.LP
\fB:= : \fImty ref * mty \(-> unit\fR
.in -0.5i
.LP
.NH 2
Notes on Built-in Functions
.LP
The function \fBload\fR loads an ML file. It takes a pair as argument
where the first component is the file name and the second is a
boolean (\fBtrue \fR= loaded functions are printed on standard output,
\fBfalse \fR= no printing).
.LP
.in +0.5i
\fBload ("file",true)
.in -0.5i
\fRNote that the system automatically adds the suffix ".ml" to the
file name.
.LP
The function \fBcompile\fR loads and compiles an ML file. Same rules
apply for the boolean argument.
.LP 
The functions \fBloadt\fR and \fBcompilet\fR take a string as an argument.  
Same effect as the functions above, but with the boolean argument set to true.
Also \fBuse\fR is a synonym for \fBloadt\fR.
.LP
The function \fBsys\fR admits the user to run a 
.UX
command from ML.
Could be useful, for example,  if one wishes to edit and load a file 
without leaving LCF. For the editor \fIvi\fR the following function:
.LP
.in +0.5
\fBfun \fRedit_load (file:string) = (\fBsys \fR("vi " ^ file ^ ".ml") ; \fBload \fRfile);
.in -0.5i
.LP
would edit and load the file \fIfile\fR by side-effect.
.LP
The function \fBsave\fR takes a file name as an argument and saves the
current state of a session as a new image on the file. This image is
quite big (> 3.5 Mb) so beware!
.in +0.5i
.LP
\fBsave \fR"state_before_coffee_break";
.in -0.5i
.LP	
.NH
LCF
.LP
The LCF part of the system is a conversion of the old Cambridge LCF and hence, 
the names of functions, types and constants remain basically the same. 
However, there are some changes that a user of the old system should notice.
.LP
.NH 2
Changes
.LP
\(bu The object-language quotation symbol in Cambridge LCF:    " 
is now:    `   (ie backquote).
.LP
\(bu The ML \fBprint\fR function can take LCF objects of the following
types as argument: \fIterm, form, thm, type \fRand \fRgoal.\fR
.LP
\(bu Makestring cannot be applied to LCF objects.
.LP
\(bu Type variables in PPLAMBDA are now the same as in ML: 'a, 'b, etc ...
.LP
	Example: `x==y : 'a`;
.LP
\(bu Comments are allowed in PPLAMBDA and are enclosed by (* and *).
.LP
Example: `x== (* this is a comment *) y`;
.LP
\(bu The LCF function # is now called // ( # may not be used in identifier).
.LP
\(bu PROVE_HYP is now called CUT
.LP
\(bu STRIP_ASSUME_TAC is now called STRIP_THM_TAC
.LP
\(bu ASSUME_TAC is now called CUT_THM_TAC
.LP
\(bu Type operator # in PPLAMDA is now * as in ML
.LP
\(bu New function : \fBtop_thm : \fI unit \(-> thm\fR (top thm on stack)
.LP
\(bu The variables goals, backup_list_limit and backup_list are
now references and their values are accessed by the function "!".
.LP
\(bu The "failwith" expressions in old LCF has been replaced by the
following exceptions:
.in +0.5i
1) \fBgeneral \fR: general exception raised in list processing etc.
(Type \fIstring\fR).
.LP
2) \fBtheory  \fR: exception raised by functions in the theory package. 
(Type \fIstring)\fR.
.LP
3) \fBrule    \fR: exception raised by inference rules.
(Type \fIstring * thm list\fR).
.LP
4) \fBtactic  \fR: exception raised by tactics.
(Type \fIstring * goal list\fR).
.LP
5) \fBsyntax\fR: exception raised when PPLAMDA syntax errors are
are detected at run-time. (Type\fI string)\fR.	
.in -0.5i
.LP
\(bu The functions \fBml_curried_infix\fR and \fBml_paired_infix\fR 
are no longer used for infixing ML functions but the ML directive
\fBinfix\fR should be used instead.
.LP
\(bu The following new tactics have been added by L. Paulson:
.in +0.5i
.LP
1) CONJ_LEFT_TAC : tactic for conjunction-left (splits conjunctive assumption in two)
.LP
2) DISJ_LEFT_TAC : tactic for disjunction-left (case split on a disjunctive assumption)
.LP
3) IMP_LEFT_TAC : tactic for implication-left (backwards chaining on an implicative assumption)
.LP
4) FORALL_LEFT_TAC : tactic for forall-left (instantiate universal assumption)
.LP
5) EXISTS_LEFT_TAC : tactic for exists-left (eliminate existential assumption)
.in -0.5i
.LP
.NH
Building the System
.LP
\(bu Move into the directory \fIFranz\fR.
.LP
\(bu Remove all object files by typing: 
.in +0.5i
rm *.o	
.in -0.5i
.LP
\(bu Change the value of the variable %help-dir, in
file S-site.l,  to a new appropriate
name. This variable points to the directory where the help information
is stored;  default 
.in +0.5i
.LP
/usr/lib/lcf/Help 
.in -0.5i
.LP
\(bu Build LCF by typing: 
.LP
.in +0.5i
make lcfc
.in -0.5i
.LP
This will compile all lisp and ML files. The name of the binary image created
is  \fIlcf\fR.
.LP
Warning: All ML files (ie *.ml) must be compiled at the same time, so 
do NOT compile and include an ML file in the system separately
once the system has been built. This will cause errors!!
(This does not apply to your own files, of course)
.LP
After an alteration of a lisp file, the system may be rebuilt by:
.in +0.5i
.LP
make lcf
.LP
.in -0.5i
this is much quicker since the ML files are not recompiled.
Standard ML may be built as a separate image. This is done by typing:
.LP
.in +0.5i
make smlc
.LP
.in -0.5i
The name of the image is \fIsml\fR.
.LP
Building LCF or ML produces rather a lot of output, so it's a good
idea to redirect the output to a separate log file for later
investigation.
.LP
Search for the key word \fIfailed\fR for finding ML errors in the log
file, and \fIError\fR for lisp errors in the same file.
.LP	
\(bu Finally, move the manual files sml.1 and lcf.1 to /usr/man/man1
and the lcf or/and sml images to a public binary directory.
.NH
Using the System
.LP
Once LCF or ML have been built, it can now be run by typing
\fIlcf\fR or \fIsml\fR respectively.
.LP
The system will respond by printing a banner and giving a prompt:
.LP
.in +0.5i
\fB# SML (RAL 1.5) #
.LP
!
.LP
\fRor:
.LP
\fB# LCF (RAL 1.5) #
.LP
!
.in -0.5i
.LP
\fRThe system is now ready and waiting for input. 
.LP
To leave either of the systems (LCF or ML), type:
.LP
.in +0.5i
quit();
.LP
.in -0.5i
or simply type ^D twice (one ^D puts you into lisp)
.LP
If by any reason the system fails and puts you into lisp, typing
the lisp expression:
.LP
.in +0.5i
(tml)	;puts you back to ML (or LCF) again, or
.LP
(quit)  ;leaves the system completely.
.LP
.in -0..5i
To test the system, move into the directory
\fIExamples\fR and type "make test".
This Makefile constructs theories about fixedpoints, truth values, equality,
lists, numbers, and so on.
.LP
It would be wise to install directory \fIExamples\fR as
/usr/lib/lcf/Examples so that users may adopt these standard theories
in their own work.
.LP
.NH
Bug Reports
.LP
Should you find any bugs, or if you have any queries, do not hesitate to
get in touch with me on :
.LP
JANET : lev@uk.ac.rl.ib
.LP
Mikael Hedlund 
.br
c/o Lilian Valentine
.br
Software Engineering Group
.br
Rutherford Appleton Laboratory
.br
Informatics Division
.br
Chilton, Didcot
.br
OX11 0QX
.br
Tel: 0235 219 00
