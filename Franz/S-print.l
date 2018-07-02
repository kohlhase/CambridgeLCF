;***********************************************************************
;*
;*	S-print
;*
;************************************************************************
;print-functions, types/values
; Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile)
  (special val thistydec thisdec thisexdec pt ty)
  (include S-constants)
  (include llmac)
  (include S-macro)
  (genprefix print))


;*	PRINTMTY
;***********************************************************************
;print ml types
(de printmty (ty flg)
 (cond
	;flg=nil => suppress expansion of abbrevated type!
   ((if flg (condpstring (getdeftype ty %temt))))
   ((mlink ty);explicit type variable
	(pstring (car ty)));
   ((selectq (car ty)
	(mk-funtyp
	   (pbegin 1)
	   (ptoken |(|)
	   (printmty (cadr ty) flg)
	   (ptoken | -> |)
	   (pbreak 0 0); **
	   (printmty (caddr ty) flg)
	   (ptoken |)|)
	   (pend))
	(mk-tupletyp
	 (cond ((eq (length (cdr ty)) 1); {#1:ty}
	   (pbegin 1)(ptoken |{|)(ptoken |#1:|)(printmty (cadr ty) flg)(ptoken |}|))
	  (t
	   (pbegin 1)
	   (ptoken |(|)
	   (printmty (cadr ty) flg);print first element
	   (mapc '(lambda (ty) (ptoken | * |)
	   (pbreak 0 0) (printmty ty flg))(cddr ty))
	   (ptoken |)|))
	  );end cond
	  (pend)
	  (pbreak 0 0))
	((mk-recordtyp mk-wildrecordtyp)
	   (if (null (cdr ty)) (ptoken |unit|)
		   (pbegin 1)
		   (ptoken |{|)
		   (pstring (caadr ty));print first label
		   (ptoken |:|)
		   (printmty (cdadr ty) flg);and associated type expression
		   (mapc 
		     '(lambda (ty) 
			(ptoken |,|)
			(pstring (car ty))
			(ptoken |:|)
			(printmty (cdr ty) flg)
		      );end lambda
		      (cddr ty)
		   );end mapc
		   (cond ((eq (car ty) 'mk-wildrecordtyp)
			(ptoken |,|)
			(ptoken | ... |))
		   );end cond
		   (ptoken |}|)
		   (pend)
	   ));end if
	(mk-wildtupletyp
	   (let ((n 0))
		(pbegin 1)
		(ptoken |{|)
	        (pstring (concat '|#| (setq n (add1 n))))
		(ptoken |:|)
		(printmty (cadr ty) flg)
		(mapc
	           '(lambda (ty) 
		      (ptoken |,|)
		      (pstring (concat '|#| (setq n (add1 n))))
		      (ptoken |:|)
		      (printmty ty flg))
	            (cddr ty)
		);end mapc
	   	(ptoken |,|)(ptoken |...|)
	        (ptoken |}|)
	      ));end let
        (t;unique symbol (includes list and ref)
	   (if (cdr ty);arguments!
		(printdatatype (cdr ty) (get (car ty) 'tyname))
		(pstring (get (car ty) 'tyname))
	   ));end if
      ));end selectq
 );end cond  
);end printmty

;***********************************************************************
;*	CONDPSTRING
;***********************************************************************
(de condpstring (str)
;print typeid and instantiated type variables if arity>0
   (if (cdr str) 
	(printdatatype 
		    (mapcar 
				;(car x)<> nil if tyvar is instantiated!
		        '(lambda (x) (if (cdr x) (cdr x) x))
		         (cdr str)
		     );end mapcar 
		     (car str)
	 );end printdatatype
	 (if str (pstring (car str)));else print typeid only
   );end if
   str;return str
);end condpstring

;***********************************************************************
;*	PRINTDATATYPE
;***********************************************************************
(de printdatatype (args typ)
    (pbegin 0)
    (cond
	((cdr args);more than one argument
	   (pbegin 1)
	   (ptoken |(|)
	   (printmty (car args) %temt)
	   (mapc '(lambda (ty) (ptoken |,|)
	             (pbreak 1 0) (printmty ty t))(cdr args))
	   (ptoken |)|)
	   (pend)
	   (pbreak 1 0))
	(args (printmty (car args) t) (pbreak 1 0))
    );end cond
    (pstring typ)
    (pend)
);end

;***********************************************************************
;*	GETDEFTYPE
;***********************************************************************
;expand type abbrevation
(de getdeftype (ty env)
 (cond
   ((null env) (get_globaldefty ty))
   ((get_inenv ty (car env)))
   ((getdeftype ty (cdr env)))
 );end cond
);end getdeftype

;***********************************************************************
;*	GET_GLOBALDEFTY
;***********************************************************************
;global defintion
(de get_globaldefty (ty)
   (getdeftype1 ty %deftypes)
);end 

;***********************************************************************
;*	GET_INENV
;***********************************************************************
;local definition, (or dec sequence)
(de get_inenv (ty env)
  (getdeftype1 ty env)
);end get_inenv

;***********************************************************************
;*	GETDEFTYPE1
;***********************************************************************
;return '(typeid . (arg_l)) where arg_l is ass list of instantiated tyvars
(de getdeftype1 (ty env )
  (cond
   ((null env) nil)
   ((let ((defty (get (cdar env) 'abbrevtyp))
	;arg_l associates tyvars and their instances
	  (arg_l (mapcar '(lambda (x) (cons x nil)) (get (cdar env) 'tyvarl))))
     (if defty;could be a type constr decl in datatype dec!
        (if (equal (cdar env)
	    (gettypetid (caar env) %temt));most recent occurrence?
	   (if (same_type ty defty arg_l) ;in wich case ty=defty!
		(cons (caar env) arg_l));return type
         );end if
     );end if
    ));end let
   ((getdeftype1 ty (cdr env)))
 );end cond
);end getdeftype1

;***********************************************************************
;*	SAME_TYPE
;***********************************************************************
;ckeck if ty1 and ty2 are the same type
;side effect:type variables in ty1 gets instantiated by using rplacd.
(de same_type (ty1 ty2 arg_l)
   (cond
	((null ty1) (if (null ty2) t))
	((mlink ty2) (ifn (occursbt ty2 ty1);typevar in ty1
		(rplacd (assoc (car ty2) arg_l) ty1)));explicit type variable
	((equal ty1 ty2))
	((atom (car ty1)) 
	   (if (equal (car ty1) (car ty2))
		(cond 
	          ((eq (car ty1) 'mk-recordtyp)
	              (if (eq (length (cdr ty1)) (length (cdr ty2)))
		         (forall
		           '(lambda (x)
			     (same_type (cdr x) (assoc1 (car x) (cdr ty2)) arg_l)
		            );end lambda
		       	    (cdr ty1)
		          );end exists
	              ));end if
	           ((same_type (cdr ty1) (cdr ty2) arg_l))
		);end cond
	    ));end if
	((and (same_type (car ty1) (car ty2) arg_l)
	      (same_type (cdr ty1) (cdr ty2) arg_l)))
   );end cond
);end same_type

;******************************************************************************
; macro for printing subtrees
(eval-when (compile load)
  (defun expand-print (x)
    (cond ((numberp x) `(print-nth ,x))
	  ((atom x) `(llprinc ',x))
	  (t x)))
  (defmacro pml l (cons 'progn (mapcar 'expand-print l))))

;***********************************************************************
;*	PRINT-NTH
;***********************************************************************
(de print-nth (n)
    (print-ml-cases (car (nthcdr n %ex)) %print-depth))

;***********************************************************************
;*	PRINT-ML-CASES
;***********************************************************************
;deparse ml parse-tree
(de print-ml-cases (%ex %print-depth)
   (if (atom %ex) (llprinc %ex)
      (selectq (car %ex)
	(mk-vartyp (pml 1))
	(mk-consttyp
	   (cond
		((null (cddr %ex)) (llprinc (cadr %ex)))
		(t
		   (if (eq (length (cddr %ex)) 1)
			(print-ml1 (car %ex))
		        (print-ml-list (cddr %ex) '|(| '|,| '|)|)
		   );end if
		   (llprinc (cadr %ex)))
	   ));end cond

; LCF stuff:
	(mk-tyquot (pml |` : ... `| ))
	(mk-quot (pml |` ... `| ))

	(mk-recordtyp (print-ml-record (cdr %ex) '|:| 'mk-recordtyp))
	(mk-tupletyp (print-ml-tuple (cdr %ex) '|*|))
	(mk-funtyp (pml |(| 1 | -> | 2 |)|))
	((mk-intconst mk-realconst) (pml 1))
	(mk-stringconst (pml |"| 1 |"|))
	(mk-boolconst (if (cadr %ex) (llprinc '|true|) (llprinc '|false|)))
	(mk-empty (llprinc '|()|))
	((mk-var mk-con mk-const) (pml 1))
	((mk-opvar mk-opcon mk-opconst) (llprinc '| op |)(pml 1))
	(mk-record (pml (print-ml-record (cdr %ex) '|=| 'mk-record)))
	(mk-tuple (pml (print-ml-tuple (cdr %ex) '|,|))	)
	(mk-list (pml (print-ml-list (cdr %ex) '|[| '|,| '|]|)))
	(mk-expseq 
	   (print-ml-list (append (cadr %ex) (cddr %ex)) '|(| '|;| '|)|))
	(mk-appn (pml |(| 1 | | 2 |)|))
	(mk-infappn (pml |(| 2 | |) (llprinc (cadadr %ex)) (pml | | 3 |)|))
	(mk-straint (pml |(| 1 |:| 2 |)|))
	(mk-andalso (pml 1 | andalso | 2))
	(mk-orelse (pml 1 | orelse | 2))
	(mk-handle (pml 1) (llprinc '| handle |) (print-handle (cddr %ex)))
	(mk-withhand
	   (llprinc (cadr %ex))
	   (llprinc '| with |)
	   (print-ml-match (cddr %ex)))
	(mk-wildhand
	   (llprinc (cadr %ex))
	   (pml | => |)
	   (print-ml-cases (caddr %ex) %print-depth))
	(mk-univhand
	   (llprinc '|? => |)
	   (print-ml-cases (cadr %ex) %print-depth))
	(mk-raise (pml | raise | 1)
		  (if (cddr %ex) (print-ml-cases (caddr %ex) %print-depth)))
	(mk-if (pml |if | 1 | then | 2 | else | 3))
	(mk-while (pml |while | 1 | do | 2))
	(mk-let (pml |let | 1 | in | 2 | end |))
	(mk-case (pml |case | 1 | of | ) (print-ml-match (cddr %ex)))
	(mk-fn (llprinc '|(|) (pml |fn |) 
	       (print-ml-match (cdr %ex)) (llprinc '|)|))
	(mk-wildcard (pml |_|))
	(mk-laypat (pml 1 | as | 2))
	(mk-val (pml |val ... |))
	(mk-fun (pml |fun ... |))
	(mk-type (pml |type ... |))
	(mk-datatype (pml |datatype .. .|))
	(mk-abstype (pml |abstype ... |))
	(mk-exception (pml |exception ... |))
	(mk-local (pml |local | 1 | in | 2 | end |))
	(mk-infix (pml |infix ... |))
	(mk-infixr (pml |infixr ... |))	
	(mk-nonfix (pml |nonfix ... |))
	(mk-decseq 
	   (cond
	 	((cdr %ex) 
		   (print-ml-cases (cadr %ex) %print-depth)
		   (mapc
			'(lambda (x)(llprinc '|;|)(print-ml-cases x %print-depth))
			 (cddr %ex)
		   ));end mapc
		(t (llprinc '| |))
	   ));end cond
     );end selectq
   );end if
);end print-ml-cases

;***********************************************************************
;*	PRINT-ML-RECORD
;***********************************************************************
(de print-ml-record (l del mark)
   (if (null l)
	(if (eq mark 'mk-recordtyp) (llprinc '|unit |) (llprinc '|{}|))
	(llprinc '|{|)
	(llprinc (if (num_labp (caar l)) (concat sharp_sym (caar l)) (caar l)));label
	(llprinc del)
	(print-ml1 (cdar l))
	(mapc
	   '(lambda (x)
		(llprinc '|,|)
	  	(llprinc (if (num_labp (car x))
			(concat sharp_sym (car x)) (car x)));numeric or alpha. label
		(llprinc del)
		(print-ml1 (cdr x))
	    );end lambda
	    (cdr l)
	);end mapc
	(llprinc '|}|)
   );end if
);end prin-ml-record

;***********************************************************************
;*	PRINT-ML-TUPLE
;***********************************************************************
(de print-ml-tuple (l del)
  (cond 
    ((eq (length l) 1);   {#1:ty}
	(llprinc '|{|)(llprinc '|#1=|)(print-ml1 (car l))(llprinc '|}|))
    (t 
	   (llprinc '|(|)
	   (print-ml1 (car l))
	   (mapc
		'(lambda (x) (llprinc del) (print-ml1 x))
		  (cdr l)
	   );end mapc
	   (llprinc '|)|))
  );end cond
);end print-ml-tuple
	
;***********************************************************************
;*	PRINT-ML-HANDLE
;***********************************************************************
;print parse-tree for handle expression
(de print-handle (l)
   (print-ml-cases (car l) %print-depth)
   (mapc
	'(lambda (x) (llprinc (concat '| | handle_sym '| |))
		     (print-ml-cases x %print-depth))
	(cdr l)
   );end mapc
);end print-handle

;***********************************************************************
;*	PRINT-ML-MATCH
;***********************************************************************
(de print-ml-match (funcase-list)
    (print-ml-funcase (car funcase-list))
    (mapc '(lambda (funcase) (llprinc (concat '| | singlebar_sym '| |))
			     (print-ml-funcase funcase))
	  (cdr funcase-list))
);end print-ml-match

;***********************************************************************
;*	PRINT-ML-FUNCASE
;***********************************************************************
(de print-ml-funcase (funcase)
    (print-ml1 (car funcase))
    (llprinc '| => |)
    (print-ml1 (cdr funcase)))			;print-ml-funcase

;***********************************************************************
;*	PRINT-ML-TEXT
;***********************************************************************
; entry point, binding %print-depth
(de print-ml-text (ex %print-depth) 
    (print-ml1 ex))				;print-ml-text

;***********************************************************************
;*	PRINT-ML1
;***********************************************************************
(de print-ml1 (ex)
    (cond ((atom ex) (llprinc ex))
	  ((zerop %print-depth) (llprinc '| ... |))
	  (t (print-ml-cases ex (sub1 %print-depth)))))	;print-ml1

;***********************************************************************
;*	PRINT-ML-LIST
;***********************************************************************
(de print-ml-list (l open sep close)
    (llprinc open)
    (when l					; just brackets if empty list
      (print-ml1 (car l))
      (mapc '(lambda (x) (llprinc sep) (print-ml1 x)) (cdr l))
      (llprinc close)))				;print-ml-list


;**********************************************************************
;functions for printing result at top level


;***********************************************************************
;*	PRINTDEC
;***********************************************************************
;print result of declaration
(de printdec (pt thistydec thisdec thisexdec val ty)
   (printdec1 )
);end printdec 

;appropriate free variables are reduced after printing a declaration.
;this is necessary when printing the result of a declaration sequence!
;one could have done it in the entry for mk-decseq, but that creates
;a problem of reduction when a local dec is within the decseq!
(de printdec1 () 
   (selectq (car pt)
	((mk-val mk-fun) 
		(printval (cdaar val) (cadr val) ty)
		(setq thisdec (cdr thisdec) val (cons (cdar val) (cddr val))))
	(mk-local (let ((pt (caddr pt))) (printdec1)));print non-local dec!
	(mk-datatype 
		(printdatatyp (car thisdec))
		(setq thisdec (cdr thisdec) thistydec (cdr thistydec)))	
	(mk-type 
		(printtyp (car thistydec))	
		(setq thistydec (cdr thistydec)))	
	(mk-abstype (let ((pt (caddr pt))) (printdec1))) ;print dec!
	(mk-exception 
		(printexception (car thisexdec))
		(setq thisexdec (cdr thisexdec) val (cons (cdar val) (cddr val))))	
	((mk-infix mk-infixr)
	  (mapc 
	    '(lambda (ix) 
		(pstring (if (eq (car pt) 'mk-infix) '|- infix | '|- infixr |))
		(pstring ix)(pnewline)
	     );end lambda
	     (cddr pt)
	   ));end mapc
	(mk-nonfix
	   (mapc
		'(lambda (nx)
		   (ptoken |- nonfix |)
		   (pstring nx)
		   (pnewline)
		 );end lambda
		 (cdr pt)
	   ));end apc
	(mk-decseq
		(let ((decl (cdr pt)) (tyl (cdr ty)) 
		;reverse to get correct order:
		     (val (if val (cons (reverse (car val))
					(reverse (cdr val)))))
		     (thisdec (reverse thisdec))
		     (thistydec (reverse thistydec))
		     (thisexdec (reverse thisexdec)))
		    (while decl
		         (let ((pt (car decl)) (ty (car tyl))) (printdec1));end let
			   (setq decl (cdr decl) tyl (cdr tyl))
		      );end while
		 ));end let
      );end selectq
);end printdec

;***********************************************************************
;*	PRINTEXCEPTION
;***********************************************************************
;print result of exception declaration.
(de printexception (exdec)
   (mapc
     '(lambda (expair)
	(ptoken |- exception |)
	(pstring (car expair))
	(ptoken | : |)
	(printmty (cdr expair) t)
	(pnewline)
      );end lambda
      exdec
    );end mapc
);end printexception

;***********************************************************************
;*	PRINTDATATYPE
;***********************************************************************
;print result of datatype declaration.
(de printdatatyp (dec)
   (mapc
     '(lambda (con)
	(ptoken |- constructor |)
	(pstring (car con))
	(ptoken | : |)
	(printmty (get (car con) 'mlcontype) t)
	(pnewline)
       );end lambda
       (reverse (cdr dec))
    );end mapc	
);end printdatatyp
		

;***********************************************************************
;*	PRINTTYPE
;***********************************************************************
;print result of type declaration.
(de printtyp (tydec)
   (mapc 
     '(lambda (typair) 
	(ptoken |- type |)
	(pstring (car typair))
	(ptoken | = |)
	(pbreak 0 0)
	(printmty (get (cdr typair) 'abbrevtyp) nil);suppress expansion
	(pnewline)
       );end lambda
       tydec
   );end mapc
);end printtyp

;***********************************************************************
;*	PRINTVAL 
;***********************************************************************
;print result of type declaration
(de printval (ids vals tys)
  (cond
	((null ids))
	((atom ids);single identifier
	   (unless (memq ids '(%wild %con %const));dont print constant!
		(ptoken |- val |)
		(pstring ids)
		(ptoken | = |)
		(pbreak 0 0)
		(printvalty vals (tidy (find_type ids %thisdec)));
	   ));end unless
	((eq (car ids) rec);recursive binding
	  (if (atom (cddr ids)) ;single binding
	    (printval (cadr ids) vals tys)
	    (let ((l (cdr ids)) (ty (cdr tys)))
		(while l
		   (printval (caar l) (car vals) (car ty))
		   (setq l (cdr l) vals (cdr vals) ty (cdr ty))
		);end while
	      );end let
	   ));end ifn
	((eq (car ids) record);record!
	   (mapc
		'(lambda (x)
		    (printval (cdr x) (assoc1 (car x) (cdr vals))
				      (assoc1 (car x) (cdr tys))
		    );end printval
		  );end lambda
		  (cdr ids)
	     ));end mapc
	((eq (car ids) lay);layered pattern
		(printval (cadr ids) vals tys)
		(printval (caddr ids) vals tys))
	(t
	   (printval (car ids) (car vals) (cadr tys))
	   (printval (cdr ids) (cdr vals)
		(if (eq (car tys) 'list) tys (cons (car tys) (cddr tys)))))
    );end cond
);end printval

;return type of i.
;must write special function since tenv is now nil!
(de find_type (i thisdec)
  (cond
   ((and (eq (caar thisdec) 'val);id is variable
	 (assoc1 i (cdar thisdec)));search for i in first layer
	(tidy (assoc1 i (cdar thisdec))));found !
   (t (find_type i (cdr thisdec)))
  );end cond
);end find_type

;***********************************************************************
;*	PRINTVALTY
;***********************************************************************
;print variable and its type
(de printvalty (id ty)
   (printml id ty nil)
   (pbreak 0 0)
   (ptoken | : |)
   (printmty ty t)
   (pnewline)
);end printvalty

;***********************************************************************
;*	PRINTML	
;***********************************************************************
;print ml value according to type
(de printml (arg ty cl)
   (cond  
     ((isabstype ty) (ptoken |-|));dont print hidden constructors
     ((or (eq (car ty) 'ref) (isdatatype ty));visable constructors!
	(if (atom arg) 
	   (ifn cl (pstring arg) (ptoken |(|) (pstring arg) (ptoken |)|))
	   (when cl (ptoken |(|))
	   (pstring (car arg))
	   (ptoken | |)
	   (printml (cdr arg) 
	   ;substitute type variable with proper types
		(cadr 
		(let ((%generic));we must set %generic temp. to nil because
		;possible explicit type variable in type of constructor
		;may be instantiated, in which case mutant would give
		;tidy would replace with new explicit type variable
		;(eg. if we print (ref 1), tyvar 'a is instant. to (int) !)
		  (expand_type 
			(tidy (getid_typ (car arg) 'con)) 
		        (get (car ty) 'tyvarl)
			(cdr ty)
			t;indicates internal repr. of ty.
		   );end expand_type
		 );end let
		);end cadr 
		t
	   );end printml
	   (when cl (ptoken |)|))
	));end if
     (t	
	(selectq (car ty)
	   (int (printnum arg))
	   (real (printnum arg))
	   (string (printstring1 arg))
	   (bool (printbool arg))
	   (list (printlist arg (cadr ty)))
	   (mk-recordtyp (printrecord (if (cdr ty) (cdr arg));could be unit!
			 (cdr ty)))
	   (mk-tupletyp (printtuple arg (cdr ty)))
	   (mk-funtyp (ptoken |fn|))

; LCF stuff
	   (term (ml-print_term arg))
	   (form (ml-print_form arg))
	   (type (ml-print_type arg))
	   (thm (ml-print_thm arg))
	));end selectq
   );end if
);end printml

;***********************************************************************
;*	ISABSTYPE
;***********************************************************************
(de isabstype (ty) 
  (eq (car (explode-word (car ty))) 'abstype)
);end isabstype

;***********************************************************************
;*	ISDATATYPE
;***********************************************************************
(de isdatatype (ty)
   (eq (car (explode-word (car ty))) 'datatype)
);end isdatatype

;***********************************************************************
;*	PRINTNUM PRINTBOOL PRINTSTRING
;***********************************************************************
(de printnum (x) (ifn (minusp x) (pstring x) (ptoken |~|) (pstring (abs x))))
(de printbool (b) (if b (ptoken true) (ptoken false)))
(de printstring (s) (pstring s));can be used for built-in function print!
(de printstring1 (s) (ptoken |"|) (pstring s) (ptoken |"|))

;***********************************************************************
;*	PRINTLIST
;***********************************************************************
(de printlist (l ty)
   (pbegin 1)
   (ptoken |[|)
   (cond
	(l 
	   (printml (car l) ty nil)
  	   (mapc 
		'(lambda (x) (ptoken |,|) (pbreak 0 0)(printml x ty nil))
		  (cdr l)
	   ));end mapc
    );end cond
    (ptoken |]|)
    (pend)
);end printlist

;***********************************************************************
;*	PRINTTUPLE
;***********************************************************************
(de printtuple (l ty)
 (pbegin 1)
 (cond
   ((eq (length l) 1) ; {#1=exp} - special case
       (ptoken |{|)(ptoken |#1=|)(printml (car l) (car ty) nil)(ptoken |}|))
   (t
	   (ptoken |(|)
	   (printml (car l) (car ty) nil)
	   (setq l (cdr l))
	   (setq ty (cdr ty))
	   (while l
		(ptoken |,|)
	        (pbreak 0 0)
		(printml (car l) (car ty) nil)
		(setq l (cdr l)) (setq ty (cdr ty))
	   );end while
	   (ptoken |)|))
   );end cond
   (pend)
);end printtuple

;***********************************************************************
;*	PRINTRECORD
;***********************************************************************
(de printrecord (l ty)
   (pbegin 1)
   (ptoken |{|)
   (cond (l
	   (pstring (caar l))
	   (ptoken |=|)
	   (printml (cdar l) (cdar ty) nil)
	   (setq l (cdr l)) (setq ty (cdr ty))
	   (while l
		(ptoken |,|)
		(pstring (caar l))
		(ptoken |=|)
		(printml (cdar l) (cdar ty) nil)
		(setq l (cdr l)) (setq ty (cdr ty))
	   ));end while
   );end cond
   (ptoken |}|)
   (pend)
);end printrecord
	  

;***********************************************************************
;*	PRINTIT
;***********************************************************************
;print value of top-level expression
(de printit (val ty)
   (ptoken |- it =|)
   (pbreak 1 0)
   (printml val ty nil)
   (pbreak 0 0)
   (ptoken | : |)
   (printmty ty t)
   (pnewline)
);end  

