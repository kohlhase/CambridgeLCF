;*****************************************************************************
;*
;*	S-dml
;*
;*****************************************************************************
; define predefined ml functions and types
; Origin: EDINBURGH LCF (Milner,Gordon,Wadsworth...) 
; Modified: CAMBRIDGE LCF (Huet,Paulson,Cousineau...) 
; Mikael Hedlund, Rutherford Appleton Lab. (1986)
;

(eval-when (compile)
  (include llmac)
  (include S-macro)
  (include S-constants)
  (*lexpr concat)
  (genprefix dml)  
);end eval-compile


;***********************************************************************
;define predeclared types and constructors

(setq %deftypes nil)

;tycon    	: list of type constructors
;l 		: ( (const constr_info mlinfix prec_lev mlcontype) .. )
;constr_info 	: (tycon . no_of_tyvars)
;mlinfix 	: ({l/r} . prec_lev(sml)) 
;mlcontype 	: representation of tycons's type.
;constr_l 	: ((con1 . arity) .. )
;abbtyp 	: rhs of type declaration
;arity 		: number of type variables
;tyname 	: name of tycon. In the case of predecl. tycons, tycon itself.

;*****************************************************************************
;*	PRETYCON
;*****************************************************************************
(de pretycon (tycon l constr_l abbtyp arity)
    (if l
	   (mapc
		'(lambda (x)
		    (if (cadr x) (putprop (car x) (cadr x) 'constr_info))
		    (if (caddr x) (putprop (car x) (caddr x) 'mlinfix))
		    (if (cadddr x) (putprop (car x) (cadddr x) 'prec_lev))
		    (if (caddddr x) (putprop (car x) (caddddr x) 'mlcontype))
		);end lambda
		l
	     );end mapc
     );end if
     (newl %deftypes `(,tycon . ,tycon));extend global environment
     (putprop tycon arity 'arity)
     (putprop tycon tycon 'tyname)
     (putprop tycon constr_l 'constr)
     (putprop tycon t 'equality); equality admited!
);end 

;define ref
(pretycon '|ref| `((ref (ref . 1) nil nil
		(mk-funtyp (|'a|) (ref (|'a|))))) `((ref . 1)) nil 1)
(putprop '|ref| '(ref) 'constructors)
(putprop '|ref| '(|'a|) 'tyvarl)
   
;define list
(pretycon
	'|list|
	`((|::| (list . 1) (r . 5) ,inf_lev 
		(mk-funtyp (mk-tupletyp (|'a|) (list  (|'a|))) (list (|'a|))))
	 (nil (list . 0) nil nil (list (|'a|))))
	 `((nil . 0) (|::| 1));constr_l
	  nil;abbtyp
	1; arity
);end pretycon list

;define unit
(pretycon '|unit| nil nil 'unit  0)

;define bool
(pretycon
	'|bool|
	`((true (bool . 0) nil nil (bool))
	  (false (bool . 0) nil nil (bool)))
	`((false . 0) (true . 0));constr_l
	 nil; abbtyp
	 0;arity
);end pretycon bool	

;define int
(pretycon '|int| nil nil nil 0)

;define real
(pretycon '|real| nil nil nil 0)
 
;define string
(pretycon '|string| nil nil nil 0)

;LCF tycons:

;define obj
(pretycon '|obj| nil nil nil 0)

;define thm
(pretycon '|thm| nil nil nil 0)

;define term 
(pretycon '|term| nil nil nil 0)

;define form
(pretycon '|form| nil nil nil 0)

;define type
(pretycon '|type| nil nil nil 0)


;***********************************************************************
;define types for functions implemented in the compiler

;*****************************************************************************
;*	DEFTYP
;*****************************************************************************
(de deftyp (f ty)
   (putprop f ty 'mlvartype)
);end deftyp

;*****************************************************************************
;*	DEFINFPREC
;*****************************************************************************
;define infix precedence
(de definfprec (f ass p)
   (putprop f inf_lev 'prec_lev)
   (putprop f `(,ass . ,p) 'mlinfix);association . precedence
);end def


;* := *
;obs: check for monotype is done in type checker!
(deftyp assign_sym '(mk-funtyp (mk-tupletyp (ref (|'a|)) (|'a|))  (mk-recordtyp)))
(definfprec assign_sym 'l 3)

;* = *
(deftyp eq_sym '(mk-funtyp (mk-tupletyp (|'ety|) (|'ety|)) (bool)))
(definfprec eq_sym 'l 4)

;* <> *
(deftyp '|<>| '(mk-funtyp (mk-tupletyp (|'ety|) (|'ety|)) (bool)))
(definfprec '|<>| 'l 4)

;* print *
(deftyp '|print| '(mk-funtyp (|'a|) (|'a|)))

;* makestring *)
(deftyp '|makestring| '(mk-funtyp (|'a|) (string)))


;**********************************************************************
;define predeclared functions and constants


;*****************************************************************************
;*	DECLARE0-ML-FUN
;*****************************************************************************
(de declare-ml-fun (ml-fn n lisp-fn mty)
    (putprop ml-fn (cons lisp-fn n) 'numargs)
    (putprop ml-fn mty 'mlvartype)
    ml-fn)					;declare-ml-fun


;*****************************************************************************
;*	DECLARE-ML-CONST
;*****************************************************************************
; define an ML constant in terms of a Lisp constant
(de declare-ml-const (id exp mty)
    (putprop id (eval exp) 'mlval)
    (putprop id mty 'mltype)
    id
);end						; declare-ml-const
 
;*****************************************************************************
; overloaded functions

;  |*|
(putprop '|*| '(mk-funtyp (mk-tupletyp (|'num|) (|'num|)) (|'num|)) 'mlvartype)
(putprop '|*|  '((int . (times . 2)) (real . (times . 2))) 'overload)
(definfprec '|*| 'l 7)

; |+|
(putprop '|+| '(mk-funtyp (mk-tupletyp (|'num|) (|'num|)) (|'num|)) 'mlvartype)
(putprop '|+| '((int . (plus . 2)) (real . (plus . 2))) 'overload)
(definfprec '|+| 'l 6)

; |-|
(putprop '|-|  '(mk-funtyp (mk-tupletyp (|'num|) (|'num|)) (|'num|)) 'mlvartype)
(putprop '|-| '((int . (difference . 2)) (real . (difference . 2))) 'overload)
(definfprec '|-| 'l 6)

; |~| unary minus
(putprop '|~| '(mk-funtyp (|'num|) (|'num|)) 'mlvartype)
(putprop '|~| '((int . (minus . 1)) (real . (minus . 1))) 'overload)

(putprop '|abs| '(mk-funtyp (|'num|) (|'num|)) 'mlvartype)
(putprop '|abs| '((int . (abs . 1)) (real . (abs . 1))) 'overload)

(putprop '|>| '(mk-funtyp (mk-tupletyp (|'nums|) (|'nums|)) (bool)) 'mlvartype)
(putprop '|>| 
  '((int . (greaterp . 2)) (real . (greaterp . 2)) (string . (greatstrp . 2))) 
  'overload)
(definfprec '|>| 'l 4)

(putprop '|<| '(mk-funtyp (mk-tupletyp (|'nums|) (|'nums|)) (bool)) 'mlvartype)
(putprop '|<|
  '((int . (lessp . 2)) (real . (lessp . 2)) (string . (lesstrp . 2))) 
  'overload)
(definfprec '|<| 'l 4)

(putprop '|>=| '(mk-funtyp (mk-tupletyp (|'nums|) (|'nums|)) (bool)) 'mlvartype)
(putprop '|>=| 
   '((int . (>= . 2)) (real . (>= . 2)) (string . (greqstrp . 2))) 'overload)
(definfprec '|>=| 'l 4)

(putprop '|<=| '(mk-funtyp (mk-tupletyp (|'nums|) (|'nums|)) (bool)) 'mlvartype)
(putprop 
   '|<=| '((int . (<= . 2)) (real . (<= . 2)) (string . (leeqstrp . 2))) 'overload)
(definfprec '|<=| 'l 4)


;*****************************************************************************
;non-overloaded functions

(dml |/| 2 realdiv (mk-funtyp (mk-tupletyp (real) (real)) (real)))
(definfprec '|/| 'l 7)

(dml |div| 2 intdiv (mk-funtyp (mk-tupletyp (int) (int)) (int)))
(definfprec '|div| 'l 7)

(dml |^| 2 concat (mk-funtyp (mk-tupletyp (string) (string)) (string)))
(definfprec '|^| 'l 6)

(dml |mod| 2 mod (mk-funtyp (mk-tupletyp (int) (int)) (int)))

(dml |@| 2 append (mk-funtyp (mk-tupletyp (list (|'a|)) (list (|'a|)))
			     (list (|'a|))))
(definfprec '|@|  'l 5)

(dml |not| 1 not (mk-funtyp (bool) (bool)))

(dml |rev| 1 reverse (mk-funtyp (list (|'a|)) (list (|'a|))))

(dml |real| 1 float (mk-funtyp (int) (real)))

(dml |sqrt| 1 sqrt (mk-funtyp (real) (real))) 

(dml |sin| 1 sin (mk-funtyp (real) (real)))

(dml |arctan| 1 arctan (mk-funtyp (real) (real)))

(dml |cos| 1 cos (mk-funtyp (real) (real)))

(dml |exp| 1 exp (mk-funtyp (real) (real)))

(dml |ln| 1 log (mk-funtyp (real) (real)))

(dml |chr| 1 ml-chr (mk-funtyp (int) (string)))

(dml |ord| 1 ml-ord (mk-funtyp (string) (int)))

(dml |explode| 1 ml-explode (mk-funtyp (string) (list (string))))

(dml |implode| 1 ml-implode (mk-funtyp (list (string)) (string)))

(dml |floor| 1 fix (mk-funtyp (real) (int)))

(dml |infprec| 1 infprec (mk-funtyp (string) (int)))

;***********************************************************************
;misc. functions

(dml |vi| 1 ml_vi (mk-funtyp (string) (mk-recordtyp)))

(dml |sys| 1 ml_sys (mk-funtyp (string) (mk-recordtyp)))

(de ml_sys (s) (let ((code `(exec ,s))) (eval code)))

(de ml_vi (s) 
    (let ((code `(exec vi ,(concat s '|.ml|))))
	     (eval code)
	     (ml-load s t)
	     (llterpri) 
    );end let
);end ml_vi


;***********************************************************************
;standard exceptions
; We declare them in lisp so that the unique symbols that represents the 
; the exceptions will be the same as the exception itself!
; Useful when matching exceptions in lisp.
;	general : string (covers all other exceptions)

(setq global%env '(()))

(setq %exceptions 0)

;define exceptions of type unit:
(de defex (id_l)
 (mapc '(lambda (ex) (defexty ex '(mk-recordtyp))) id_l );end mapc
);end defex

(de defexty (exn ty)
	(putprop exn exn 'exname)
	(putprop exn ty  'extyp)
	(setq global%env (cons `(,exn ,exn . %exc) global%env))
	(eval `(setq ,exn ',exn))
);end defexty

(defex '(ord |chr| |*| |/| |div| |mod| |+| |-| |floor| |sqrt| |exp| |ln| |interrupt| |load| |compile| |match| |bind| |lisperror| |implode|))

(defexty '|general| '(string))


;functions
;***********************************************************************
(de print_num (n) (pstring n))		; ml-print_int

(de print_string (tok) (ptoken |"|) (pstring tok) (ptoken |"|))	;ml-print_tok

(de print_bool (b) (if b (ptoken true) (ptoken false)))	;ml-print_bool

(de print_unit (ignore) (ptoken |{}| ))	;ml-print_void

 
; define print_string and print_int (necessary for pretty_printing)
(dml |print_string| 1 pstring (mk-funtyp (string) (mk-recordtyp)))
(dml |print_int| 1 pstring (mk-funtyp (int) (mk-recordtyp)))


(de arctan (x) (atan x 1.0))

(de infprec (s) (cdr (get s 'mlinfix)))

(de ml-chr (n)
    (if (or (< n 0) (> n 127)) (failwith '|chr|) (ascii n)))	; ml-chr

(de ml-ord (c)
   (if (null c) (failwith '|ord|) (cascii c))
);end ml-ord

(de intdiv (x y)
   (if (zerop y)
       (failwith '|div|)
       (*quo x y)))

(de realdiv (x y)
    (if (zerop y)
	(failwith '|/|)
	(quotient x y)))			;div

(de ml-explode (tok)
    (mapcar 'ascii (exploden tok)))		;ml-explode

(de ml-implode (l)
    (if (forall '(lambda (x) (eq (length (exploden x)) 1)) l)
	(concatl l)
	(failwith '|implode|)))			;ml-implode

; string > string
(de greatstrp (s1 s2) (not (lesstrp s1 s2)))

; string < string
(de lesstrp (s1 s2)
   (let ((s1l (explode s1)) (s2l (explode s2)))
	(prog ()
%lessploop%
	 	(cond
		   ((not s2l) (return nil)); ie. "aab" < "aa" is false
		   ((lessp (cascii (car s1l)) (cascii (car s2l)))
			(return t)); ie "a" < "b" is true
		   ((greaterp (cascii (car s1l)) (cascii (car s2l)))
			(return nil)); ie "b" < "a" is false
		);end cond
		(setq s1l (cdr s1l) s2l (cdr s2l))
		(if s1l (go %lessploop%))
	        (if s2l (return t);ie "aa" < "aab" is true
		   (return nil); ie s1 = s2
	   );end if
	);end prog
   );end let
);end lesstrp

; string <= string
(de leeqstrp (s1 s2)
   (let ((s1l (explode s1)) (s2l (explode s2)))
	(leeqstrp1 s1l s2l)
   );end let
);end leeqstrp

(de leeqstrp1 (l1 l2)
   (cond
	((and (not l1) (not l2)) t); s1 equal s2!
	((not l1) t); s1<s2 !
	((not l2) nil) ; s1 > s2 !
	((or
	   (and (eq (cascii (car l1)) (cascii (car l2)));first chrs equal!
		(leeqstrp1 (cdr l1) (cdr l2));check other chars
	   );end and
	   (lessp (cascii (car l1)) (cascii (car l2)))))
   );end cond
);end leeqstrp1

; string >= string
(de greqstrp (s1 s2)
   (let ((s1l (explode s1)) (s2l (explode s2)))
	(greqstrp1 s1l s2l)
   );end let
);end greqstr

(de greqstrp1 (l1 l2)
   (cond
	((and (not l2) (not l1)) t); s1 = s2
	((not l1) nil); l1 < l2
	((not l2) t); l1 . l2
	((or
	   (and (eq (cascii (car l1)) (cascii (car l2)));first chrs eq
	         (greqstrp1 (cdr l1) (cdr l2))); and rest ok!
	   (greaterp (cascii (car l1)) (cascii (car l2)))));end or
   );end cond
);end greqstr1 


;********************************************************************
;define ml infixes

(de def_mlinfix (op_l prec_l ass)
   (mapc
	'(lambda (x)
		(putprop x `(,ass . ,prec_l) 'mlinfix);infix status
	   	(def_prec x inf_lev);global prec. lev.
	);end lambda
	op_l
   );end mapc
);end def_mlinfix

(def_mlinfix '( / div mod *) 7 'l)
(def_mlinfix '( + - ^ ) 6 'l)
(def_mlinfix '( |::| ) 5 'r)
(def_mlinfix '(=  <> < > <= >=) 4 'l)
(def_mlinfix '( |:=| ) 3 'l)

;********************************************************************

(defconst tokempty '|""|)


;*********************************************************************
