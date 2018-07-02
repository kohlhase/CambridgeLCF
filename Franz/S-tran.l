;************************************************************************
;*
;*	S-tran.l
;*
;***********************************************************************
;translate ml to lisp
;Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile)
(include S-constants)
(include llmac)
(include S-macro))



;***********************************************************************
;*	FUNCTIONS
;***********************************************************************

; recognize %val bindings (and AVOID taking car of atoms!!!)
(de is_val (x) (and (consp x) (eq (car x) val)))

;***********************************************************************
;*	GET_LISP_BINDING
;***********************************************************************
;get binding of exception or value id in env.
(de get_lisp_binding (i mark env)
   (cond
	((null env) nil)
	((and (eq (caar env) i)
	      (eq (cddar env) mark)
	 );end and
	   (cadar env))
	(t (get_lisp_binding i mark (cdr env)))
   );end cond
);end get_lisp_binding

;***********************************************************************
;*	GET_VAL_BINDING
;***********************************************************************
;get binding of value id in global environment
(de get_val_binding (i)
   (get_lisp_binding i val global%env)
);end

;***********************************************************************
;*	GET_EXC_BINDING
;***********************************************************************
;get binding of exception name in global environment
(de get_exc_binding (i)
   (get_lisp_binding i exc global%env)
);end

;***********************************************************************
;*	STORES
;***********************************************************************
;produce code for assignment
(de stores (var arg)
    (cond
	((stores1 var arg));local
	(t
	   (let ((v (get_val_binding var)))
		`(rplacd ,v ,arg)
	   ));end let
   );end cond
);end stores

;***********************************************************************
;*	STORES1
;***********************************************************************
;produce code for assignment in let expression or local dec
(de stores1 (var arg)
   (let ((path (access_var var)))
	(ifn (null path)
	   `(rplacd ,(cdr path) ,arg)
        );end ifn
   );end let
);end stores1

;******************************************************************************
;functions for translating the predeclared function print and makestring.


;*************************************************************************
;*	TR_MAKESTR
;*************************************************************************
;generate a function that takes an object as input and outouts a string!
(de tr_makestr (arg ty)
   (let ((%stringfns %stringfns) (ty (tidy ty)));strip out mlinks.
	(selectq (car ty);
	   ((int real) `(concat ,arg))
	   (bool `(cond (,arg '|true|) (t '|false|)))
	   (string `(concat '|"| ,arg '|"|))
	   (list (tr_makestrlist arg (cadr ty)))
	   (mk-tupletyp (tr_makestrtuple arg (cdr ty)))
	   (mk-recordtyp (tr_makestrrecord `(cdr ,arg) (cdr ty)))
	   (mk-funtyp `(quote |fn|))
	   (t; unique symbol
		(cond
		   ((assoc1 ty %stringfns);recursive type (already processed)
			;apply argument to already existing function
			`(,(assoc1 ty %stringfns) ,arg))
		   ((isabstype ty); hidden constructor (abstype)
			'(quote |-|));
		   ((or (eq (car ty) 'ref) (isdatatype ty));visible constr.
		;add new function too association list
			(newl %stringfns `(,ty . (lambda (x)))) 
		;generate function for this type constructor
			(let ((makefn (tr_makestrdatatype arg ty)))
			   ;replace in place (create circular list)
			   ;add paren this time : con (con arg)
			   (rplacd (cdr (assoc1 ty %stringfns))
				   `(,makefn )
			   );end rplacd
			   makefn; return
			));end let
		   ));end cond
	);end selectq
   );end let
);end tr_makestr

;*************************************************************************
;*	TR_MAKESTRTUPLE
;*************************************************************************
; (exp1,..,expn) -> "(exp1, .. ,expn)"
(defun tr_makestrtuple (arg ty)
  (cond
	((eq (length ty) 1); special case: {#1=exp}
	   `(concat '|{#1=|
	          ((lambda (x) ,(tr_makestr 'x (car ty))) (car ,arg));
		 '|}|
	   ));end concat	
	(t; tuple
	   `(concat '|(| 
	      ((lambda (x) ,(tr_makestr 'x (car ty))) (car ,arg));first elem.
	      (concatl (mapcar 'eval ;evaluate all function applications
		,(prog (l) 
	           (setq ty (cdr ty) arg `(cdr ,arg))
		   (while ty
		       (newr l 
			`(concat '|,| 
	                   ((lambda (x) ,(tr_makestr 'x (car ty))) (car ,arg));
			 );end concat
		       );end newr
	               (setq ty (cdr ty) arg `(cdr ,arg))
		   );end while
		   (return `(quote ,l))
		);end prog
	      ));end concatl
	      '|)|
	  ));end concat 
   );end cond
);

;*************************************************************************
;*	TR_MAKESTRLIST
;*************************************************************************
;[exp1, ... ,expn] -> "[exp1, ... ,expn]"
(defun tr_makestrlist (arg ty)
;generate makestr function for an element in list:
 (let ((makefn (tr_makestr 'x ty)))
      `(cond (,arg ;not [].
	      (concat '|[| ((lambda (x) ,makefn) (car ,arg));apply first element
		   (concatl
			(mapcar 
		           '(lambda (x) (concat '|,| ((lambda (x) ,makefn ) x)))
			    (cdr ,arg)
			);end mapcar
		   );end concatl
		'|]|
	     ));end concat
	 (t '|[]|)
       );end cond
   );end let
);end tr_makestrlist

;*************************************************************************
;*	TR_MAKESTRRECORD
;*************************************************************************
;* {lab1=exp1, ... ,labn=expn} -> "{lab1=exp1, ... ,labn=expn}"
(de tr_makestrrecord (arg ty)
   (cond
	((eq (length ty) 0) `(quote |{}|)); unit
	(t	
	   `(concat '|{| (caar ,arg) '|=| ; : "{label1="
	     ((lambda (x) ,(tr_makestr 'x (cdar ty))) (cdar ,arg)) 
	     ,(if (cdr ty);more than 1 element?
		`(concatl (mapcar 'eval; evaluate function applications
		     ,(prog (l)
		   	(setq ty (cdr ty) arg `(cdr ,arg))
			(while ty;iterate over each element:
			   (newr l;accumulate functions in l
				`(concat '|,| (caar ,arg) '|=| ; : ",label="
	                           ((lambda (x) 
				     ,(tr_makestr 'x (cdar ty))) (cdar ,arg)) 
				 );end concat
			    );end newr
			    (setq ty (cdr ty) arg `(cdr ,arg))
			);end while
			(return `(quote ,l))
		     );end prog
		));end concatl
		`(quote ||); else empty string
	      );end if
	      '|}|
	   ));end concat
   );end cond
);end tr_makestrrecord
	
;*************************************************************************
;*	TR_MAKESTRDATATYPE
;*************************************************************************
;* Generate lisp condition with entry for all associated constructors with tycon
;* For a recursive type (eg datatype foo= .. | con of foo | ... the 
;* output will affectively be a circular list. %stringfns is a global ass list
;* that associates tycons with string functions (used for recursive types!)
;* Correct function is chosen at run time.
(de tr_makestrdatatype (arg ty)
   (let 
      ((makefn; generate an entry in cond for each constructor
		;and create a function for the constructor.
		;correct function is hence chosen at run time!
	(cons 'cond
	   (mapcar; map over a list of all associated constructors
		'(lambda (c)
			;get type of constructor(strip out mlinks)
		   (let ((ty1 
		       (let ((%generic nil)) (tidy (getid_typ c 'con)))))
	        ;must set %generic temporal. to nil since
		;possible explicit type variable in type of constructor
		;may be instantiated, in which case 
		;tidy would replace with new explicit type variable
		;(eg. if we print (ref 1), tyvar 'a is instant. to (int) !)
		      (let ((ty2; type of argument to non-nullary constr
			(cadr
			   ;substitue tyvars with types
			   (expand_type
				ty1; type of constructors (non-instantiated)
				(get (car ty) 'tyvarl); list of ass. tyvars
				(cdr ty);list of types
				t; indicate internal repr. of type
			   );end expand_type
		 );end let
			 );end cadr
			);end ty2
		      (cond
			((eq (car ty1) 'mk-funtyp);non-nullary constr: (con arg)
			   `((eq ',c (car ,arg));correct constructor?
				(concat 
		;should c be a constr. of type foo -> foo , paranthesis are
		;included in the function stored in %stringfns(see tr_makestr)
		;else include paranthesis here!
				   (car ,arg);constructor	
				    '| | '|(| ,(tr_makestr `(cdr ,arg) ty2);argument
				    '|)|
				 )));end concat
			 (t ;nullary constructor
			   `((atom ,arg) (concat ,arg)))
		      );end cond
	            );end let
		  );end let
		);end lambda
		(get (car ty) 'constructors); associated constructors
	   );end mapcar
	)));end makefn
	makefn; return
   );end let
);end tr_makestrdatatype	

;***********************************************************************
;*	TR_PRINT
;***********************************************************************
;generate a print function
(de tr_print (arg ty cl); cl=t -> print paranthesis in tr_printdatatype
  (let ((ty (tidy ty)) (%printfns %printfns))
   (selectq (car ty)
	((int real) `(printnum ,arg));see print.l
; to print a string without quotes, change printstring1 to printstring
	(string `(printstring1 ,arg))
	(bool `(printbool ,arg))
	(list (tr_printlist arg (cadr ty)))
	(mk-tupletyp (tr_printtuple arg (cdr ty)))
	(mk-funtyp '(ptoken |fn|))
	(mk-recordtyp (tr_printrecord `(cdr ,arg) (cdr ty)))

;LCF objects: (necessary for printing objects passed with exceptions)
	(thm `(ml-print_thm ,arg))
	(form `(ml-print_form ,arg))
	(goal `(progn ,(tr_print `(car ,arg) '(list (form)))
			(ptoken | * |)
			,(tr_print `(cadr ,arg) (form))))
	(type `(ml-print_type ,arg))
	(term `(ml-print_term ,arg))


	(t; unique symbol
	   (cond
		((assoc1 ty %printfns);recursively defined (see below)
				;apply lambda fn to argument:
			`(,(assoc1 ty %printfns) ,arg))
		((isabstype ty);hidden constructor(abstype decl.)
		   '(ptoken |-|)) ;dont print!
		((or (eq (car ty) 'ref) (isdatatype ty));visible constr.
			;save prfn in case of recursive type.
	;copy necessary to avoid same lisp structure!
		  (newl %printfns `(,ty . ,(copy '(lambda (x)))))
		  (let ((prfn (tr_printdatatype arg ty t)))
		;replace with correct print function(affected if recursive type)
		;(ie datatype foo=con1| .. |conn of .. foo ..)
		;this creates a circular list.
		    	(rplacd (cdr (assoc1 ty %printfns)) `(,prfn))
			prfn; return prfn
		  ));end let 
	    ));end cond
   );end selectq
 );end let
);end tr_print

;***********************************************************************
;*	TR_PRINTDATATYPE
;***********************************************************************
;generate print function for value constructor (nullary)
;or application of non-nullary value contructor and substitute
;type variables used in declaration of type (if any) with real types.
(de tr_printdatatype (arg ty cl)
	;generate a print func. for every associated constructor
	;with tycon, correct func. is selected at run time!
	(let ((prfn
		(cons 'cond
		   (mapcar;map over all constructors
		     '(lambda (c)
		         (let ((ty1 
			   (let ((%generic nil)) (tidy (getid_typ c 'con)))))
		;we must set %generic temporal. to nil since
		;possible explicit type variable in type of constructor
		;may be instantiated, in which case 
		;tidy would replace with new explicit type variable
		;(eg. if we print (ref 1), tyvar 'a is instant. to (int) !)
			     (let
				 ((ty2
				     (cadr
			;substitute type variabes with real types:
					(expand_type
				           ty1;	
					   (get (car ty) 'tyvarl)
					   (cdr ty);list of real types
					   t;indicate intern. repr. of ty
					);end expand_type
			);end let
				    );end cadr
				);end ty2
			     (cond
			      ((eq (car ty1) 'mk-funtyp);
			       `((eq ',c (car ,arg));correct constructor?
				;non-nullary
				   (pstring (car ,arg));print constructor
				   (ptoken | |)
				   ,(ifn (eq (car ty2) 'mk-tupletyp);paren printed
				      '(ptoken |(|);by print-tuple-function
				      '(ptoken ||); (see tr_printtuple)
				    );end if
				   ,(tr_print
				    `(cdr ,arg)
				     ty2
				    t ;print paranthesis next time!
				  );end tr_print
				   ,(ifn (eq (car ty2) 'mk-tupletyp);paren printed
				      '(ptoken |)|);by print-tuple-function
				      '(ptoken ||); (see tr_printtuple)
				    );end if
			        ));end c
			      (t; nullary constructor
			       `((atom ,arg) (pstring ,arg)))
			      );end cond
			     );end let
			 );end let
		      );end lambda
		     (get (car ty) 'constructors)
		   );end mapcar
		)));end cons
		prfn;return print function
      );end let
);end tr_printdatatype

;***********************************************************************
;*	TR_PRiNTLIST
;***********************************************************************
(de tr_printlist (arg ty)
  (let ((pfn (tr_print 'x ty nil)));generate print function
   `(progn
	(pbegin 1)
	(ptoken |[|)
	(cond
	   (,arg; not empty list
		   ((lambda (x) ,pfn) (car ,arg));first element
		      (mapc
			'(lambda (x)
			   (ptoken |,|)
			   (pbreak 0 0)
			   ,pfn
			 );end lambda
			 (cdr ,arg)
		      );end mapc
	           );end arg
	);end cond
	(ptoken |]|)
	(pend)
    );end progn
  );end let
);end tr_printlist

;***********************************************************************
;*	TR_PRINTRECORD
;***********************************************************************
(de tr_printrecord (arg ty)
   (let ((prfn '((ptoken |{|) (pbegin 1) progn)))
      (cond
        (ty
		(newl prfn `(pstring ',(caar ty)))
		(newl prfn '(ptoken |=|))
		(newl prfn '(pbreak 0 0))
		(newl prfn 
		   `((lambda (x) ,(tr_print 'x (cdar ty) nil)) (assoc1 ',(caar ty) ,arg))
		);end newl
		(setq ty (cdr ty))
		(while ty
		   (newl prfn '(ptoken |,|))
		   (newl prfn '(pbreak 1 0))
		   (newl prfn `(pstring ',(caar ty)))
		   (newl prfn '(ptoken |=|))
		   (newl prfn '(pbreak 0 0))
		   (newl prfn 
		     `((lambda (x) ,(tr_print 'x (cdar ty) nil)) (assoc1 ',(caar ty) ,arg))
		   );end newl
		   (setq ty (cdr ty))
	        ));end while
	);end cond
	(newl prfn '(ptoken |}|))
	(newl prfn '(pend))
	(reverse prfn);
   );end let
);end tr_printrecord

;***********************************************************************
;*	TR_PRINTTUPLE
;***********************************************************************
(de tr_printtuple (arg ty)
  (if (eq (length ty) 1); special case: {#1=exp}
     (let ((prfn '((ptoken |#1=|) (ptoken |{|) (pbegin 1) progn)))
	(newl prfn (tr_print `(car ,arg) (car ty) nil))
	(newl prfn '(ptoken |}|))
	(reverse prfn)
      );end let
      (let ((prfn '((ptoken |(|) (pbegin 1) progn))); else ordinary tuple!
	(newl prfn `((lambda (x) ,(tr_print 'x (car ty) nil)) (car ,arg)))
	(setq ty (cdr ty) arg `(cdr ,arg))
	(while ty
	   (newl prfn '(ptoken |,|))
	   (newl prfn '(pbreak 0 0))
	   (newl prfn `((lambda (x) ,(tr_print 'x (car ty) nil)) (car ,arg)))
	   (setq ty (cdr ty) arg `(cdr ,arg))
	);end while
	(newl prfn '(ptoken |)|))
	(newl prfn '(pend))
	(reverse prfn)
      );end let
   );end if
);end tr_printtuple

;***********************************************************************
;*	TR_EQUALITY
;***********************************************************************
;generate equality function
(de tr_equality (x y ty)
  (let ((ty (tidy ty)))
   (selectq (car ty)
	(ref `(eq ,x ,y))
	((int bool string real) `(equal ,x ,y))
	(mk-tupletyp
	   (cons 'and (tr_equalityt x y (cdr ty))))
	(mk-recordtyp
	   (cons 'and (tr_equalityr `(cdr ,x) `(cdr ,y) (cdr ty))))
	(list (tr_equalityl x y (cadr ty)))
	(t; unique symbol! constant or application of constructor!
		(let ((con_ty (car %coneq_l)))
		   (setq %coneq_l (cdr %coneq_l));remove top layer!
		   (if (eq (car con_ty) 'mk-funtyp);con of funtype(non-nullary)?
			;remove constructor and compare args to constr:
			(tr_equality `(cdr ,x) `(cdr ,y) (cadr con_ty))
			;else constant (nullary):
			`(equal ,x ,y)
		   );end if
		));end let
   );end selectq
 );end let
);end tr_equality

;***********************************************************************
;*	TR_EQUALITYT
;***********************************************************************
(de tr_equalityt (x y ty)
   (let ((l))
	(while ty
	   (newl l (tr_equality `(car ,x) `(car ,y) (car ty)))
	   (setq x `(cdr ,x))(setq y `(cdr ,y))(setq ty(cdr ty))
	);end while
	l;return l
   );end let
);end tr_equalityt

;***********************************************************************
;*	TR_EQUALITYL
;***********************************************************************
(de tr_equalityl (x y ty)
	;generate a testfunction for the elements in the list
   (let ((test (tr_equality `(car xx) `(car yy) ty)))
     `(prog (xx yy)
       (setq xx ,x)(setq yy ,y)
%loppa%
	(cond
	   ((atom xx) (return (equal xx yy))); empty list !
	   ((not ,test) (return nil));some elements not eq!
	   ((null xx) (return t));all elements tested!
	 );end cond
	(setq xx (cdr xx))(setq yy (cdr yy))
	(go %loppa%);next element in the list
    );end prog	
  );end let
);end tr_equality

;***********************************************************************
;*	TR_EQUALITYR
;***********************************************************************
(de tr_equalityr (x y ty)
   (let ((l))  
    (while ty
	(newl l 
	   (tr_equality 
              `(assoc1 ',(caar ty) ,x) 
	      `(assoc1 ',(caar ty) ,y) 
	       (cdar ty)
	    );end 
	);end newl
	(setq ty (cdr ty))
     );end while
     l;return l
   );end let
);end tr_equalityr 


;***********************************************************************
;*	PRIMVAL
;***********************************************************************
;primitive function or value
(de primval (i ty)
    (cond ((null i) nil)			
	  ((get i 'numargs);ordinary predecl. func. 
		   (qeval (mkclosure i ty)))
	  ((get i 'mlvartype) `(get ',i 'mlval))	
    );end cond
);primval

;***********************************************************************
;*	FAP
;***********************************************************************
; Direct application of dml'd functions
;
(de fap (n a r)
    (cond
      ((zerop n) r); no arguments
      ((= n 1) (nconc r (list a))); one arguments
      ((not (atom a)); two or several args (never more than 2 in SML core)
       (selectq (car a)
         (list (fap (sub1 n) (caddr a) (nconc r (list (cadr a)))))
         (quote 
             (fap (sub1 n) 
			(qeval (cadadr a)) (nconc r (list (qeval (caadr a))))))
        ));end selectq
      (t nil)
    );end cond
);end fap


;***********************************************************************
;*	MKCLOSURE
;***********************************************************************
(de mkclosure (i ty)
    (cond ((get i 'closure))
	  ((putprop i (lispfunclosure i ty) 'closure))
    );end cond
);mkclosure

;***********************************************************************
;*	LISPFUNCLOSURE
;***********************************************************************
;generate a closure
(de lispfunclosure (i ty)
    (let ((in  (if ty; ty<>nil if i is overloaded fun!
		;overloaded functon, choose correct function according to type:
		  (assoc1 (car (tidy ty)) (get i 'overload));
	          (get i 'numargs))));
      (cons 
	(list 'lambda '(%e) (cons (car in) (lispargs (cdr in) '(car %e)))) i)
      );end let
);lispfunclosure

;***********************************************************************
;*	LISPARGS
;***********************************************************************
;generate path in %e for arguments	
(de lispargs (n a)
  (if (= n 1) (list a) (lispargs1 n a)))

(de lispargs1 (n a)
    (cond 
	  ((zerop n) nil)
	  ((= n 1)  (list `(car ,a)))
	  (t (cons `(car ,a) (lispargs1 (sub1 n) `(cdr ,a))))
    );end cond
);lispargs


;***********************************************************************
;*	RESET_REF
;***********************************************************************
;set global flg %ref to nil.
(de reset_ref (rhs)
   (setq %ref nil)
    rhs;return rhs
);end reset_ref

;***********************************************************************
;*	BUILD_LB
;***********************************************************************
;build up structure of lisp atoms 
(de build_lb (marker bvs)
   (cond
	((null bvs) nil)
	((atom bvs);one id!
	   (if (eq bvs '%const)
		'%const
		(uniquesym marker bvs)	
	   ));end if
	((eq (car bvs) rec)
		(build_lb
		  marker
		  (if (atom (cddr bvs));single binding
			(cadr bvs)
			(mapcar 'car (cdr bvs));pick out ids!
		   );end if
		));end build_lb
	((memq (car bvs) `(,val ,exc))
		(build_lb marker (cdr bvs)))
	((eq (car bvs) lay);layered pattern
	   `(,lay ,(build_lb marker (cadr bvs)) ,(build_lb marker (caddr bvs))))
	((eq (car bvs) record)
	   (cons record
		(mapcar
		   '(lambda (x) (cons (car x) (build_lb marker (cdr x))))
		    (cdr bvs)
		);end mapcar
	    ));end cons
	(t (cons
		(build_lb marker (car bvs))
		(build_lb marker (cdr bvs))
	   ));end cons
   );end cond
);end build_lb

;***************************************************************************
;*        TESTEVAL
;***************************************************************************
(de testeval (e)
   (if (is_constant e) (qeval (eval e)) e)
);end testeval

;***************************************************************************
;*        IS_CONSTANT
;***************************************************************************
(de is_constant (e)
   (if (atom e) (or (numberp e) (memq e '(t nil)))
	(selectq (car e)
	   (quote t)
	   ((cons list) (forall 'is_constant (cdr e)))
	   (record (forall 'is_constant
		       (mapcar 'cdr (cdr e))
		    ));end forall
            (t nil)
	);end selectq
   );end if
);end is_constant

;***************************************************************************
;*        GEN_EX
;***************************************************************************
;generate exception value (0 1 2 3 4 ...
(de gen_ex ()
   (quote (concat (setq %exceptions (add1 %exceptions))))
);end gen_ex

;***************************************************************************
;*        CURRYBIND
;***************************************************************************
; If function body has the form `(cons ,fun %e)  then return "fun"
; Such bodies occur in code generated for curried ML functions
(de currybind (body)
      (ifn (atom body)			;to avoid destructuring a number
	   (let (((x-cons x-quofun x-e . l) body))	; . l to avoid errors
	     (if (and (eq x-cons 'cons)
		      (consp x-quofun)
		      (eq (car x-quofun) 'quote)
		      (eq x-e '%e))
		 (cadr x-quofun)
	     );end if
	    );end let
	);end ifn
);currybind

;***************************************************************************
;*        LOCFLG_ON LOCFLG_OFF
;***************************************************************************
(de locflg_on () (setq %loc_fundecs_flg t))
(de locflg_off (x) (setq %loc_fundecs_flg nil) x)

;***************************************************************************
;*        AP
;***************************************************************************
;call lisp funcall
(de ap (fn arg) (funcall (car fn) (cons arg (cdr fn))));fn is closure
   ;(car fn) = function, (cdr fn) = %e when fun was defined

;***************************************************************************
;*        NFIRST
;***************************************************************************
(de nfirst (l n)
    (if (eq n 0) nil
	(cons (car l) (nfirst (cdr l) (- n 1))))
);end

;***************************************************************************
;*        COMBINETREE
;***************************************************************************
(de combinetree (t1 t2)
   (cond
     ((null t1) nil)
     ((atom t1) (cons t1 t2))
     ((is_val (car t1)) (combinetree (cdar t1) t2))
     (t (cons (combinetree (car t1) (car t2))
		   (combinetree (cdr t1) (cdr t2))
         ));end cons
   );end cond
) ;end combinetree

;***************************************************************************
;*        LISPFUNPAT
;***************************************************************************
;generate a pattern of function names (lisp atoms)
(de lispfunpat (pat genfun_flg)
   (cond
	((null pat) nil)
	((atom pat) 
	   (cond
		(genfun_flg;generate unique symbol! 
		   (let ((sym (uniquesym 'fun %timestamp)))
		      (newl fun%env `(,pat . ,sym));add new layer to fun%env!
		      sym;return sym
		   ));end let
		(%loc_fundecs_flg;unique symbol already generated in tr_let
			;or tr_local (by calling bvpat)
		  
		   (assoc1 pat fun%env);fun symbol in fun%env
		  );end %loc_fundecs_flg

		(t; called from tr_vb!
	;each ml function name is given an unique symbol which forms
	;the lisp function name. This is done when bvpat is first called,
	;but since bvpat is called several times during the translation
	;of a sequence, a let expression or a local decl., a new
	;function name would be generated each time. To prevent this,
	;we store the function name and the lisp atonm in an associated list.
			    (or (cadr (access_var pat));
			        (assoc1 pat fun%env);seq., let or local!
			    );end or
		   )))
        ((is_val pat) (lispfunpat (cdr pat) genfun_flg));skip tag
	((is_val (car pat))
	   (lispfunpat (cdar pat) genfun_flg));**changed from flg -> genfun_flg
	(t (cons
		(lispfunpat (car pat) genfun_flg)
		(lispfunpat (cdr pat) genfun_flg)
	   ));end cons
   );end cond
);end lispfunpat

;***************************************************************************
;*        INSERTTRANSFUN
;***************************************************************************
;insert the generated function name (with a marker) in parse tree for fn-expression.
(de inserttransfun (e funpat)
    (selectq (car e)
       (mk-fn  `(mk-fn (%flg . ,funpat) ,(cdr e)));indicate fun name!
       (mk-tuple
          (cons 'mk-tuple
	      (prog (x y)
		  (setq x (cdr e))
		  (while x
                    (newr y (inserttransfun (car x) (car funpat)))
		    (setq x (cdr x))(setq  funpat (cdr funpat))
		   );end while
	           (return y)
		)));end prog 
       (mk-straint (inserttransfun (cadr e) funpat))
       (t (lcferror (cons e '(unknown pattern inserttransfun))))
    );end selectq
);end inserttransfun


;***********************************************************************
;* 	PATTERN FUNCTIONS
;***********************************************************************

;***************************************************************************
;*        BVPAT
;***************************************************************************
;*
;*DESCRIPTION: Create a structure of identifiers.
;*
;*COMMENTS: %val and %exc are markers to indicate form of declaration.
;*	    genfun_flg : t -> generate new function name in lispfunpat
;*						(via valpat) 
;*		         nil -> don't !
;*
;***************************************************************************
(de bvpat (dec genfun_flg)
   (selectq (car dec)
   	(mk-val `((,val . ,(valpat (cadr dec) genfun_flg))))
	(mk-fun `((,val . ,(funpat (cadr dec) genfun_flg))))
	((mk-type mk-datatype mk-infixr mk-infix mk-nonfix) nil)
	(mk-abstype (bvpat (caddr dec) genfun_flg)); bvpat[dec]
	(mk-exception `((,exc . ,(excpat (cadr dec)))))
	(mk-local (bvpat (caddr dec) genfun_flg)); bvpat[dec2]
	(mk-decseq (seqpat (cdr dec) genfun_flg))
   );end selectq
);end bvpat

;***************************************************************************
;*        SEQPAT
;***************************************************************************
;*
;*DESCRIPTION: Create a structure of identifiers out of a declaration sequence.
;*
;***************************************************************************
(de seqpat (l genfun_flg)
   (cond
	((null l) nil);empty sequence!
	((eq (length l) 1) (bvpat (car l) genfun_flg))
	(t (append (seqpat (cdr l) genfun_flg) (bvpat (car l) genfun_flg)))
   );end cond
);end seqpat

;***************************************************************************
;*	VALPAT
;***************************************************************************
;*
;*DESCRIPTION: Create a structurew of identifiers out of a value binding..
;*
;***************************************************************************
(de valpat (vb genfun_flg)
   (selectq (car vb)
	(mk-valbind (varpat (cadr vb)))
	(mk-and (mapcar '(lambda (vb) (valpat vb genfun_flg)) (cdr vb)))
	  ;create unique lisp symbols for each function name!
	(mk-rec 
	   (let ((vp (valpat (cadr vb) genfun_flg)))
		(cons rec (combinetree vp (lispfunpat vp genfun_flg)))
		;t is bvpat_flg, genfun indicates whether a new 
		;function name should be generated in lispfunpat
	    ));end
   );end selectq
);end valpat

		
;***************************************************************************
;*        FUNPAT
;***************************************************************************
;*
;*DESCRIPTION: Create a structure of identifiers out of function binding.
;*
;***************************************************************************
(de funpat (fb genfun_flg) (cons rec (funpat1 fb genfun_flg)))

(de funpat1 (fb genfun_flg)
    (selectq (car fb)
	(mk-funbind 
	 (let ((fp (cadadr fb)))
	;create unique symbols for each function name!
	    (combinetree fp (lispfunpat fp genfun_flg))
		;t is bvpat_flg, genfun indicates whether a new 
		;function name should be generated in lispfunpat
	 ));end let
	(mk-and (mapcar '(lambda (fb) (funpat1 fb genfun_flg)) (cdr fb)))
    );end selectq
);end funpat



;***************************************************************************
;*        EXCPAT
;***************************************************************************
;*
;*DESCRIPTION: Create a struture of exception names out of an exception binding.
;*
;***************************************************************************
(de excpat (eb) 
   (selectq (car eb)
	(mk-exbind
; exceptions get type unit by defaut (2/2/87)
;	   (cond
;		((atom (cadr eb));no type constraint!
;		   (cadr eb))
;		(t 
			(caadr eb)
;		);
;	   );end cond
	 );end mk-excbind
	   
	(mk-and (mapcar 'excpat (cdr eb)))
   );end selectq
);end excpat


;***************************************************************************
;*        VARPAT
;***************************************************************************
;*
;*DESCRIPTION: Create a structure of identifiers out of a pattern.
;*
;***************************************************************************
(de varpat (pat)
   (selectq (car pat)
	((mk-var mk-opvar) (cadr pat))
	(mk-wildcard '%wild)
	((mk-const mk-intconst mk-realconst mk-stringconst mk-empty
	  mk-opconst mk-opcon) '%const)

	(mk-record
	   (cond
		((num_labp (caadr pat));numeric label!
		   (mapcar;for each item in sorted record:
			'(lambda (r) (varpat (cdr r)))
			 (cdr (sort_record pat))
		   ));end mapcar
		(t ;alphabetic label
		   (cons record; indicate "alphabetic record"
			(mapcar
				;label must remain in the representation!
			   '(lambda (r) (cons (car r) (varpat (cdr r))))
			    (cdr pat)
			);end mapcar
		    ));end cons
	     ));end cond
	(mk-wildrecord
	   (cond
	 	((num_labp (caadr pat)); numeric label!
			(mapcar
	;for each item in the sorted and filled up record:
			   '(lambda (r) (varpat (cdr r)))
			 (cdr(fill_record (sort_record pat) nil));nil is flg.
			));end mapcar
		(t ;alphabetic label
		   (cons record; indicate record!
			(mapcar
			   '(lambda (r) (cons (car r) (varpat (cdr r))))
			    (cdr pat)
			);end mapcar
		   ));end cons
	   ));end cond
	((mk-list mk-tuple)
	   (mapcar 'varpat (cdr pat)))
	(mk-laypat
	   `(%lay; indicate layered pattern!
		,(cond
		   ((eq (cadr pat) 'mk-straint)
			(cadadadr pat))
		   (t (cadadr pat))
		);end cond
		,(varpat (caddr pat))
	   ));
	(mk-appn
	  (cond
		((eq (cadadr pat) cons_sym)
		   `(,(varpat (cadaddr pat)) . ,(varpat (caddaddr pat))))
		(t `(%con . ,(varpat (caddr pat))))
	   ));end cond
	(mk-infappn 
	   (varpat `(mk-appn ,(cadr pat) (mk-tuple ,(caddr pat) ,(cadddr pat)))))
	(mk-straint (varpat (cadr pat)))
   );end selectq
);end varpat


;***************************************************************************
;*        CHECK_PAT
;***************************************************************************
;*
;*DESCRIPTION: Generate code for matching patterns to expressions.
;*
;***************************************************************************
(de check_pat (pat ans)
    (let ((cl (check_p pat 'a)))
   	(if cl
	   `((lambda (a) ,(gencheck cl 'a)) ,ans)
	    ans
	);end if
     );end let
);end check_pat


;***************************************************************************
;*        CHECK_RECORD
;***************************************************************************
;*
;*DESCRIPTION: Generate code for checking a record pattern at run time.
;*
;***************************************************************************
(de check_record (pat arg)
   (selectq (car pat)
	(mk-record
	   (cond
		((num_labp (caadr pat));numeric label !
			  (check_sl 
			    (mapcar `cdr ;filter out labels
			       (cdr (sort_record pat));in sorted record
			    );end mapcar
			    arg
			  ));end checksl
		(t; alphabetic label
			  (check_rl
				(cdr pat);skip marker
				(list 'cdr arg); - " -
			  ));end check_rl
	    ));end cond
	(mk-wildrecord
	   (cond
		((num_labp (caadr pat));num. label
			(check_sl 
			   (mapcar `cdr ;filter out labels
			     (cdr (fill_record (sort_record pat) nil))
			   );end mapcar
		  	   arg
		        ));end ckeck_sl
		(t
			  (check_rl
				(cdr pat);remove label
				(list 'cdr arg); - " -
			  ));end check_sl
	   ));end cond
   );end selectq
);end check_record

;***************************************************************************
;*        CHECK_P
;***************************************************************************
(de check_p (pat arg)
   (selectq (car pat)
	((mk-empty mk-var mk-opvar mk-wildcard) nil)
	((mk-realconst mk-intconst mk-boolconst) 
	   `((eq ,(cadr pat) ,arg)))
	(mk-stringconst `((eq ',(cadr pat) ,arg)))
	(mk-const `((and (atom ,arg) (eq ',(cadr pat) ,arg))))
	(mk-list
	   (cons
	;length of list is unknown at compile time:
		`(eq (length ,arg) ,(length (cdr pat)))
		 (check_sl (cdr pat) arg)
	   ));end cons
	(mk-tuple (check_sl (cdr pat) arg))
	((mk-wildrecord mk-record)
	  (ifn (null (cdr pat))
		(check_record pat arg)
	   ));;end ifn
	(mk-appn
	   (cond
		((eq (cadadr pat) cons_sym); cons is special case:(x::l)
		  (cons arg; arg must be non-nil
		   (nconc
			(check_p (cadaddr pat) (list `car arg)); x !
			(check_p (caddaddr pat) (list `cdr arg)); l !
		   )));end nconc
		(t
		   (if (eq (cadadr pat) 'ref); reference, set %ref
			(setq %ref t)	;to avoid aliasing
		   );end if
		   (cons
			`(and
			   (eq (typep ,arg) 'list); 
			   (eq (car ,arg) ',(cadadr pat))
			 );end and
			 (check_p (caddr pat) `(cdr ,arg))
		   ));end cons	
		));end cond
	(mk-infappn
	   (check_p
	    `(mk-appn ,(cadr pat) (mk-tuple ,(caddr pat) ,(cadddr pat)))
		 arg
	    ));end check_p

	(mk-straint (check_p (cadr pat) arg))
	(mk-laypat (check_p (caddr pat) arg))
    );end selectq
);end check_p

;***************************************************************************
;*        CHECK_SL
;***************************************************************************
;*
;*DESCRIPTION: Generate check code for each element in a list or a tuple.
;*
;***************************************************************************
(de check_sl (sl arg)
    (if (null sl) 
	nil 
	(nconc
		(check_p (car sl) (list 'car arg))
		(check_sl (cdr sl) (list 'cdr arg))
	);end nconc
    );end if
);check_sl

;***************************************************************************
;*        CHECK_RL
;***************************************************************************
;*
;*DESCRIPTION: Generate check code for each component in a record.
;*
;***************************************************************************
(de check_rl (rl arg)
    (if (null rl) 
	nil 
	(nconc
		(check_p (cdar rl) `(assoc1 ',(caar rl) ,arg));find corr. element in arg.
		(check_rl (cdr rl) arg)
	);end nconc
    );end if
);check_sl

;***************************************************************************
;*        MAKE_COND_CASE
;***************************************************************************
;*
;*DESCRIPTION: Generate a lisp condition.
;*
;***************************************************************************
(de make_cond_case (cl ans)
    `(,(ifn cl t (ifn (cdr cl) (car cl) (cons 'and cl))) ,ans)
);make_cond_case
 
;***************************************************************************
;*        GENCHECK
;***************************************************************************
;generate check-code for matching patterns and expressions n bindings
;fail with 'bind' if no-match.
(de gencheck (cl ans)
    (ifn cl ans
	 `(cond
	    ,(make_cond_case cl ans)
            ((throw (cons 'pac (cons 'bind nil)) 'evaluation))
	   );end cond
    );end if
);gencheck

;***************************************************************************
;*        GENCHECKL
;***************************************************************************
;generate cde for checking patterns and expressions in matches.
;fail with 'match' if no-match.
(de gencheckl (cl-ans-list)
    `(cond
       ,@(mapcar '(lambda (p) (make_cond_case (car p) (cdr p))) cl-ans-list)
          ((throw (cons 'pac (cons 'match nil)) 'evaluation))
     );end cond
);end gencheckl

;***********************************************************************
;*	ACCESS FUNCTIONS
;***********************************************************************

;***************************************************************************
;*        ACCESS_VAR
;***************************************************************************
;access path for variable in %p
(de access_var (i)
    (let ((path (access_path i %p val)))
      (ifn (null path)
	   (cond
	     ((eq (car path) ord)	;- ordinary variable : (%ord . path)
	      (cons (car path) 
		    (access_code (reverse (cdr path)) '%e)))
	     ((eq (car path) rec);	- recursive function (%rec id . path)
	     (cons (car path)
		    (cons (cadr path)
			  (access_code (reverse (cddr path)) '%e))))
	     ((eq (caar path) record);id in record!
		 (cons record (access_recordcode path '%e))); variable found
				;in record : (%record . assocfn)
 ))));access_var

;***************************************************************************
;*        ACCESS_EXN
;***************************************************************************
;access exception id in %p.
(de access_exn (e)
    (let ((path (access_path e %p exc)))
      (ifn (null path)
	(access_code (reverse (cdr path)) '%e)
	(get_exc_binding e);top level exception!
      );end ifn
    );end let
);end access_exn

;***************************************************************************
;*        ACCESS_RECORD
;***************************************************************************
;return function to access i in record (l) if i is found in l.
(de access_record (i l)
   (cond
	((null l) nil)
	((access_path i `(,(cdar l)) val);found in first element
	    (if (atom (cdar l));
		(cons; no further path within label. cons with dummy!
		   (caar l);
;i occurs within this label but not in a nested structure. (%dummy indicates this)
		   '%dummy
		 );end cons
		 (cons
		    (caar l)
		    (access_path i (cdar l) 'val);path within label!
		 );end cons
	     ));end if
	(t (access_record i (cdr l)))
   );end cond
);end access_record

;***************************************************************************
;*        RAP
;***************************************************************************
(de rap (i rho tag)
    (let ((tac nil))
      (cond
	((eq (car rho) tag) (rap i (cdr rho)tag))
	((atom (car rho)) (if (eq (car rho) i) (cons (cdr rho) nil)))
	((eq (caar rho) tag) (rap i (cons (cdar rho) (cdr rho)) tag))
	((atom (caar rho)) 
	 (cond
	   ((eq (caar rho) i)
	    (cons (cdar rho) '(a)))
	   ((atom (cadr rho) )
	    (if (eq (cadr rho) i) (cons (cddr rho) '(d))))
	   ((setq tac (rap i (cdr rho) tag)) 
	    (rplacd tac (cons 'd (cdr tac))))))
	((setq tac (rap i (car rho) tag)) 
	 (rplacd tac (cons 'ad (cdr tac))))
	((atom (cadr rho) )
	 (if (eq (cadr rho) i) (cons (cddr rho) '(d))))
	((setq tac (rap i (cdr rho) tag)) 
	 (rplacd tac (cons 'd (cdr tac)))))))	;rap

;***********************************************************************
;*        UPD_AP
;***************************************************************************
(de upd_ap (path move)
    (cond
      ((eq (car path) rec) (rplacd (cdr path) (cons move (cddr path))) path)
      ((eq (car path) ord) (rplacd path (cons move (cdr path))))
      ((eq (caar path) record)
	   (rplacd path (cons move (cdr path))))))

;***************************************************************************
;*        ACCESS_PATH
;***************************************************************************
;*
;*DESCRIPTION: Returns a path (ie a composition of cars and cdrs) to 
;*	       an identifier in %p (and %e at run time)
;*
;***************************************************************************
(de access_path (i rho tag)
    (let ((tac nil))
      (ifn (null rho)
	   (cond
	     ((atom (car rho))
	      (cond
		((eq (car rho) i) (cons ord '(a)))
	        ((eq (car rho) record)
		   (if (and
			(eq tag val)
			(access_record i (cdr rho));search record. 
		       );end and
		     (cons `(,record . ,(access_record i (cdr rho))) '(d))))
		((eq (car rho) rec) 
		     (if (and (eq tag val) (setq tac (rap i (cdr rho) tag)))
					`(,rec . ,tac)))
		((atom (cdr rho)) 
			(if (eq (cdr rho) i)
			      (cons ord '(d))))
		((setq tac (access_path i (cdr rho) tag)) (upd_ap tac 'd))))
	     ((and ;single layered pattern 
		(eq (caar rho) lay);and layered
		(or (eq (cadar rho) i); var = id!
			;or apat is a var and is eq. to i!
		    (and (atom (caddar rho)) (eq (caddar rho) i))
		));end or
			(cons ord '(a)))
	     ((and ; single layered pattern where id may be in apat!
		(eq (caar rho) lay); layered pattern ?
	   	(not (atom (caddar rho)));apat is not a var<>id
		(setq tac (access_path i (caddar rho) tag));search apat!
	       );end and
		    (upd_ap tac 'a)); add a car 
	     ((and ;single layered pattern in a val dec
		(eq (caar rho) tag); tag is %val
		(eq (cadar rho) lay);and layered
		(or (eq (caddar rho) i); var = id!
			;or apat is a var and is eq. to i!
		    (and (atom (cadddar rho)) (eq (cadddar rho) i))
		));end or
			(cons ord '(a)))
	     ((and ; single layered pattern where id may be in apat!
		(eq (caar rho) tag); tag = %val ?
		(eq (cadar rho) lay); layered pattern ?
	   	(not (atom (cadddar rho)));apat is not a var<>id
		(setq tac (access_path i (cadddar rho) tag));search apat!
	       );end and
		    (upd_ap tac 'a)); add a car 
	     ((and;right tag followed by list of ids!
		   (eq tag (caar rho));right tag followed by
		   (not (atom (cdar rho)));list of ids
		   (setq tac (access_path i (cdar rho) tag)));skip tag
			(upd_ap tac 'a)); add a car
	     ((and;right tag followed by a single id!
		   (eq tag (caar rho));right tag
		   (atom (cdar rho));single id
		   (eq (cdar rho) i));id found !
			(cons ord '(a)));
	     ((setq tac (access_path i (car rho) tag)) 
	      (upd_ap tac 'a))
	     ((atom (cdr rho)) (if (eq (cdr rho) i)
				   (cons ord '(d))))
	     ((setq tac (access_path i (cdr rho) tag))
	      (upd_ap tac 'd))
	   );end cond
	);end ifn
    );end let
);access_path

;***********************************************************************
;*	ACCESS_CODE
;***********************************************************************
;generate composition of car and cdr.
(de access_code (l p)
    (if (null l) '%e
	(if (< (length l) 5)
	    `(,(concatl `(c ,@l r)) ,p)
	    `(,(concatl `(c ,@(nfirst l 4) r)) ,(access_code (cddddr l) p))))
);end access_code

;***************************************************************************
;*        ACESS_RECORDCODE
;***************************************************************************
;   l = ((%record . access_record[i,l]))
; where access_record[i,l]= (label' . access_path[pattern_in_label'])
;interpretation of (caar access_path[pattern_in_label'])
; record -> record within record {label={label ... id ..}}
; dummy -> id occur alone with label {label=id}
; ord -> id occurs within label but in a nested structure  {label= ... id ...}
(de access_recordcode (l p)
   (cond
	((eq (caar l) record)
	   (if (eq (cddar l) '%dummy);no path within label
		`(assoc1 ',(cadar l) ,(access_code (reverse (cdr l)) p))
		  (access_recordcode (cddar l)
				     `(assoc1 ',(cadar l) 
				       ,(access_code (reverse (cdr l)) p)
				       );end assoc1
		  );end access_recordcode
	   ));end if
	((eq (car l) ord)
	   (access_code (reverse (cdr l)) p))
   );end cond
);end access_recordcode


;***********************************************************************
;*	EXPRESSION FUNCTIONS
;***********************************************************************

;***************************************************************************
;*        TREX
;***************************************************************************
;*
;*DESCRIPTION: Add a new layer to %p and translate the expression in
;*	       the extended environment. 
;*
;***************************************************************************
(de trex (new%p e)
   (let ((%p (cons new%p %p))) 
      (tre e)
   );end let
);end trex

;***************************************************************************
;*        TR_MATCH
;***************************************************************************
;*
;*DESCRIPTION: Translate a match.
;*
;***************************************************************************
(de tr_match (fun_l)
  (let ((l
   (gencheckl
	(mapcar
	   '(lambda (fun_case)
		(cons (check_p (car fun_case) '(car %e));generate check code!
		      (trex (varpat (car fun_case)) (cdr fun_case));trans. exp!
		);end cons
	    );;end lambda
	     fun_l
	);end mapcar
   )));end gencheckl
; Changed 9/5/87 - should rewrite this stuff sometime!
   (if (eq (caadr l) 't); if first clause is exhaustive (ie. pat is a var)
	(cadadr l); then it is sufficient to return the exp. and excl. exception
	(cons (car l)
	   (mapcar ;now, strip out all t's in (t exp)
		   ;exept when exp = nil (false in SML)!
	   	'(lambda (x) 
			(if (and (eq (car x) 't) (not (eq (cadr x) 'nil)))
			  (cdr x) x)
		 );end lambda
	   (cdr l));end mapcar
	);end cons
   );end if
  );end let
);end tr_match

;***************************************************************************
;*        TR_HANDLE
;***************************************************************************
;*
;*DESCRIPTION: Generate code for handle expression.
;*
;***************************************************************************
(de tr_handle (exp l)
   `((lambda (v) 
	(cond
	   ((and 
	     (not (atom v));necessary for next check
	     (eq (car v) 'pac);packet returned from exp
	   );end and	
		;translate the handler rules
		,(tr_hrule l 'v))
	   (t v);no packet! pass value
	);end cond
       );end lambda
       (catch ,(tre exp) 'evaluation)); translate expression
);end tr_handle

;***************************************************************************
;*        TR_HRULE
;***************************************************************************
;*
;*DESCRIPTION: Generate code for handler rules.
;*
;***************************************************************************
(de tr_hrule (l v)
   (cons 'cond
	(prog (cl)
loop
	   (cond
		((null l);no more handle rules!
			;no hrule found at run time, pass packet further up
		   (newl cl `(t (throw ,v 'evaluation)))
		   (return (reverse cl)))
		((eq (caar l) 'mk-withhand)	;exn with match
		   (newl cl
			;check raised exception value with this one
			`((eq (cadr ,v) ,(access_exn (cadar l)));both exn equal?
			    ((lambda  (%e)
				,(tr_match (cddar l)); translate the match.
			    );end lambda
			    (cons (cddr ,v) %e));extend %e for matching!
		    )));end newl
		((eq (caar l) 'mk-wildhand);	exn => exp
		  (newl cl
		;check raised exception value with this one
		   `((eq (cadr ,v) ,(access_exn (cadar l)));both exn equal?
			,(tre (caddar l)));return expression!
		     ));end newl
		((eq (caar l) 'mk-univhand); ? => (catches any exception)!
		  (newl cl
		   `(t ,(tre (cadar l)));return expression!
		    ));end newl
   	   );end cond
	   (setq l (cdr l)) (go loop)
	);end prog
   );end cons
);end tr_hrule 

;***************************************************************************
;*        TR_LET
;***************************************************************************
;*
;*DESCRIPTION: Translate a let expression.
;*
;***************************************************************************
(de tr_let (dec exp);
 (let ((fun%env fun%env))
	`((lambda (%e) 
            ,(let ((%p (append (bvpat dec t) %p)));extend %p
	;t indicates that new function names (if any) should
	;be generated in lispfunpat (via bvpat)!
                 (tre exp);transl. expression
	      );end let
	   ;in the environment extended by:
	  );end lambda
	 (append ,(locflg_off (tr_dec dec (locflg_on))) %e))
  );end let
);end tr_let

;***************************************************************************
;*        TRE
;***************************************************************************
;*
;*DESCRIPTION: Translate an expression.
;*
;***************************************************************************
(de tre (pt)
   (selectq (car pt)
	((mk-intconst mk-realconst mk-boolconst) (cadr pt))

   	(mk-stringconst (qeval (cadr pt)))	

	((mk-var mk-opvar)
	    ;search for id!
	   (let ((acfn (access_var (cadr pt))))
		(cond
		   ((eq (car acfn)  ord) (cdr acfn));ordinary var!
		   ((eq (car acfn) rec) (cddr acfn));recursively defined var!
		   ((eq (car acfn) record) (cdr acfn));id within a record
		   ((get_val_binding (cadr pt)));global var!
		   ((primval (cadr pt) nil)); predeclared var.
		);end cond
	   ));end let

	((mk-const mk-opconst) `',(cadr pt))

	(mk-record
	 (ifn (null (cdr pt));not empty record
	   (cond
	  	((num_labp (caadr pt));numeric label !
		   (testeval
			(cons 'list
			  ;trans. each element in the record, skip labels!
			   (mapcar 
			     '(lambda (x) (tre (cdr x)));filter out labels.
			      (cdr (sort_record pt)));sort the record!
			);end cons
		   ));end testeval
		(t ; alphabetic label, labels must be carried to run time.
		   (testeval
			(cons 'list
			  (cons ''%record;indicate alphabetic record
			   (mapcar
			         ;save the labels!
			     '(lambda (x) `(cons ',(car x) ,(tre (cdr x))))
			      (cdr pt)
			   );end mapcar
			  );end cons
			);end cons
		   ));end testeval
		);end cond
	      ));end ifn

	((mk-tuple mk-list)
	   (testeval
		(cons 'list
		   (mapcar 'tre (cdr pt)) ;trans. each element!
		);end cons
	    ));end testeval

	(mk-expseq
	   `(cond
		(t . ,(nconc
			(mapcar 'tre (cadr pt))
			(list (tre (caddr pt)))
		      ));end nconc
	     ));end cond

	(mk-appn
	   (selectq (caadr pt)
		((mk-con mk-opcon);constructor special!
		  (cond
		    ((eq (cadadr pt) cons_sym); list special case!
			`(cons ,(tre (cadaddr pt)) ,(tre (caddaddr pt))))
		    (t `(cons ',(cadadr pt) ,(tre (caddr pt))))
		  ));end cond
		((mk-var mk-opvar)
		   (let ((acfn (access_var (cadadr pt)));search var!
			 (arg (tre (caddr pt))));transl. argument!
		     (cond
			((eq (car acfn) ord);ordinary variabe
			   `(ap ,(cdr acfn) ,arg));apply argument!
			((eq (car acfn) rec);recursively def. variable!
		;cons argument with the functions closure!
			        `(,(cadr acfn) (cons ,arg (cdr ,(cddr acfn)))));apply!
			((eq (cadadr pt) assign_sym);assignment special case!
			    ;(mk-appn (mk-var :=) (mk-tuple [var] [exp]))
			   `((lambda (a) 
			            ,(stores (cadar (cdaddr pt)) 'a) nil)
			      ,(tre (caddr (caddr pt)))))
			((eq (cadadr pt) neq_sym);equality special case!
			    ;(cddadr pt)=type of argument for "="
			  `((lambda (x)
			       (not ,(tr_equality '(car x) '(cadr x) (tidy (cddadr pt))))
			     );end lambda
			     ,arg))
			((eq (cadadr pt) eq_sym);equality special case!
			    ;(cddadr pt)=type of argument for "="
			    ; (car x) = lhs; (cadr x) = rhs 
			  `((lambda (x)
			       ,(tr_equality '(car x) '(cadr x) (tidy (cddadr pt)))
			     );end lambda
			     ,arg))
		 	((eq (cadadr pt) 'makestring);makestring special case!
			  ;tr_makestr -> (lambda (x) body)
			   `((lambda (x) ,(tr_makestr 'x (cddadr pt))) ,arg)) 
			((eq (cadadr pt) 'print);print function special case!
			   `((lambda (x)
				,(tr_print 'x (cddadr pt) nil)
				 (pnewline)
				 x;return argument
			     );end lambda
			     ,arg
			   ));end print
			((let ((lb (get_val_binding (cadadr pt))))
;added nil 7/5/87
				(if lb `(ap ,lb ,arg) nil)))
		;function is overloaded or defined by dml!
		;Note: id is overloaded fun. if (cddadr pt)=ty and <> nil 
	        ;by side effect from typechecking!
		;Possible functions with corresponding no. of args is
		;stored in the property list 'overload.
			((let ((in (or
				(assoc1 (car (tidy (cddadr pt)));overloaded
				   (get (cadadr pt) 'overload)); function!
				(get (cadadr pt) 'numargs)))); dml'd function!
			   (and (cdr in) (fap (cdr in) arg (list (car in))))))
			(`(ap ,(primval (cadadr pt)
			          (if (cddadr pt) (cddadr pt))) ,arg))
		      );end cond
		   ));end let 
		(otherwise `(ap ,(tre (cadr pt)) ,(tre (caddr pt))))
	   ));end selectq 

	(mk-infappn 
	     (tre `(mk-appn ,(cadr pt) (mk-tuple ,(caddr pt) ,(cadddr pt)))))

	(mk-straint (tre (cadr pt)))

	(mk-andalso ;translated as derived form
	   (tre `(mk-if ,(cadr pt) ,(caddr pt) (mk-boolconst nil))))

	(mk-orelse
	   (tre `(mk-if ,(cadr pt) (mk-boolconst t) ,(caddr pt))))

	(mk-raise; throw a packet,  p= (pac . (exn . value)).
	  (let ((ex (access_exn (cadr pt))))
	    `(prog2 (putprop ,ex (quote ,(cadr pt)) 'exname)
	        ,(cond
	  	    ((cddr pt);with expression
		      `(throw 
		        (cons 'pac 
			   (cons ,ex ,(tre (caddr pt)))
		        );end cons
			'evaluation
	              ));end throw
	            (t ;no expression
		     `(throw (cons 'pac (cons ,ex nil))
			'evaluation
		    ));end throw
	         );end cond
	      );end prog2
	     ));end let

	(mk-handle (tr_handle (cadr pt) (cddr pt)))

	(mk-if;translate to lisp condition!
	   `(cond
		(,(tre (cadr pt)) ,(tre (caddr pt)))
	 	(t ,(tre (cadddr pt)))
	    ));end cond

	(mk-while;translate to lisp prog!
	   `(prog () %snurra%
		(cond
		   (,(tre (cadr pt)) ,(tre (caddr pt)) (go %snurra%))
		   (t (return nil))
		);end cond
	     ));end prog

	(mk-let
	   (tr_let (cadr pt) (caddr pt)))	

; changed lambda to let 11/5/87 and back to lambda 15/5/87
	(mk-case
	   `((lambda (%e)
		,(tr_match (cddr pt))
	    );end lambda
 	    (cons ,(tre (cadr pt)) %e))
	);end mk-case

	(mk-fn
	   (let ((check_body (tr_match ;select argument for tr_match
	  ;%flg indicates that the fn-exp. occcurs in a decl. and
	  ;a prev. def. function name is included
		    (if (eq (caadr pt) '%flg);see tr_let!
				(caddr pt)
				(cdr pt)
		     )));
	  	(newfun 
		  (if (eq (caadr pt) '%flg);
		      (cdadr pt);fun name previously def! 
		      (uniquesym `fun %timestamp);else create new name
		   )));end if
	      ;lisp fun declaration to be evaluated in top loop!
	     (newl %compfns `(defun ,newfun (%e) ,check_body))
	     (eval-remember
		`(putprop ',newfun ',(currybind check_body) 'currybind)
	      );end eval... 
	      `(cons ',newfun %e);return closure!
	   ));end let

; LCF stuff
           (mk-quot
            `(qtrap #+symbolics
	       (*catch 'evaluation 
		   ((lambda (%vtyl) (quotation ,(trq (cadr pt)))) nil))
	       #-symbolics
	       (catch ((lambda (%vtyl) (quotation ,(trq (cadr pt)))) nil) evaluation)
	       ))
            (mk-tyquot `(qtrap #+symbolics
			 (*catch 'evaluation (list ,(trq (cadr pt))))
			 #-symbolics
			 (catch (list ,(trq (cadr pt))) evaluation)
			 ))
   );end selectq
);end tre
  
; LCF Stuff:

;****************************************************************************
;*	TRQ
;****************************************************************************
; translate quotation
(de trq (e)
    (let ((qfun (assq1 (car e) %q-trans-args)))
      (if qfun (cons qfun (mapcar (function trq) (cdr e)))
	  (let ((qfun (assq1 (car e) %q-quote-arg)))
	    (if qfun `(,qfun (quote ,(cadr e)))
		(selectq (car e)
		  (MK=ANTIQUOT `(q-mk_antiquot ,(tre (cadr e))))
		  (MK=TYPE=ANTIQUOT (tre (cadr e)))
		  (MK=PREDICATE
		   `(q-mk_pred (quote ,(cadr e)) ,(trq (caddr e))))
		  (MK=TYPE
		   `(q-mk_type (quote ,(cadr e))
			       (list . ,(mapcar (function trq) (cddr e))))))))))
); end trq

; translation tables for OL parse trees
; phyla for which all subtrees must be translated (via trq)
(defconst %q-trans-args
	  '(					; term constructors
	    (MK=TYPED . q-mk_typed)	
	    (MK=ABS . q-mk_abs)
	    (MK=COMB . q-mk_comb)
	    (MK=PAIR . q-mk_pair)
	    (MK=COND . q-mk_cond)
						; formula constructors
	    (MK=EQUIV . q-mk_equiv)
	    (MK=INEQUIV . q-mk_inequiv)
	    (MK=NEG . q-mk_neg)
	    (MK=CONJ . q-mk_conj)
	    (MK=DISJ . q-mk_disj)
	    (MK=IMP . q-mk_imp)
	    (MK=IFF . q-mk_iff)
	    (MK=FORALL . q-mk_forall)
	    (MK=EXISTS . q-mk_exists)))

; phyla for which the one subtree must be quoted
(defconst %q-quote-arg
	  '((MK=VAR . q-mk_var)
	    (MK=CONST . q-mk_const)
	    (MK=VARTYPE . q-mk_vartype)))

;***********************************************************************
;* 	BINDINGS
;***********************************************************************



;***************************************************************************
;*        TR_VB
;***************************************************************************
;*
;*DESCRIPTION: Translate a value binding.
;*
;***************************************************************************
(de tr_vb (vb)
 (reset_ref; %ref may have been set in check_p
   (selectq (car vb)
	(mk-valbind
	   (let ((rhs (check_pat (cadr vb) (tre (caddr vb)))))
			(if %ref;%ref set if a pattern contains application of ref.
				`(copy ,rhs);produce a copy at run time
				  rhs	    ;to avoid aliasing
			);end if
	   );end let
         );end mk-valbind
	(mk-and 
; changed 15/5/87
	   (cons 'list (mapcar 'tr_vb (cdr vb))))
	(mk-rec
	   (cond
	 	((eq (caadr vb) 'mk-valbind);single valbind
		   (let ((body
			  (let ((%p (cons (valpat vb 
				(ifn %loc_fundecs_flg t)) %p))) ;(see cmnt)
	;if %loc_fundecs_flg=nil 
	;      then the function name (=unique symbol occuring in %p)
	;      is already generated (indirectly via bvpat and lispfunpat)
	;      hence the actual parameter for genfun_flg (in bvpat via valpat) 
	;is set to nil, else generate new function name (in lispfunpat)
			      (tre; translate exp in extended env.
				  (inserttransfun (caddadr vb)
				     (lispfunpat (valpat (cadr vb) nil) nil)
				   );end inserttransfun
			      );end tre
			    );end let
		        ));end if
		;return new layer consed to %e. This forms the closure
		;for the function. 
		      `((lambda (%e) (car (rplaca %e ,body)))(cons nil %e))
		   ));end let
		((eq (caadr vb) 'mk-and)
	;cannot be done with mapcar since an extension of %e
	;caused by one binding must be known by the others!
	;format still the same though, hence no need changing bvpat!
		  (let ((l1 (split_and (cdadr vb))))
		    (let ((vb1 
		     `(mk-rec 
			 (mk-valbind 
				,(cons 'mk-tuple (car l1)) 
				,(cons 'mk-tuple (cdr l1)))
			  )));end vb1
			   (tr_vb vb1)
		    );end let
		   ));end let
	     ));end cond
   );end selectq
 );end reset_ref
);end tr_vb

;***************************************************************************
;*        TR_FB
;***************************************************************************
;*
;*DESCRIPTION: Translate a function binding.
;*
;***************************************************************************
(de tr_fb (fb)
   (selectq (car fb)
	(mk-funbind
	   (tr_vb
	;translate equivalent form of val binding
		`(mk-rec ,(adjust_clause (cdr fb)));
	   ));end tr_vb
	(mk-and 
	    (tr_vb
	      `(mk-rec 
		  ,(cons 'mk-and 
		     (mapcar 
			'(lambda (x) (adjust_clause (cdr x)))
			 (cdr fb)
		     );end mapcar
		   );end cons
		);end mk-rec
	    ));end tr_vb
    );end selectq
);end tr_fb

;***************************************************************************
;*        TR_EB
;***************************************************************************
;*
;*DESCRIPTION: Translate an exception binding.
;*
;***************************************************************************
(de tr_eb (eb)
    (selectq (car eb)
	(mk-exbind
             (cond
		((cddr eb);non-generative!
		   (access_exn (caddr eb)));get old exception
		(t (gen_ex));generate new exception
	     ));end cond
	(mk-and `(mapcar 'eval ',(mapcar 'tr_eb (cdr eb))))
   );end selectq
);end tr_eb

;***********************************************************************
;*	DECLARATIONS
;***********************************************************************


;***************************************************************************
;*        TR_LOCAL
;***************************************************************************
;*
;*DESCRIPTION: Translate a local declaration.
;*
;***************************************************************************
(de tr_local (l)
  (let ((fun%env fun%env))
	;translate dec2 in the environment extended by dec1:
	`((lambda (%e) 
	    ,(let ((%p (append (bvpat (car l) t) %p)));extend %p
	;true indicates that new function names (if any) should
	;be generated (in lispfunpat)!
		(tr_dec (cadr l) nil)
	     ));end let
		;%loc_fundecs_flg indicates that %p has been extended!
		;checked in lispfunpat!
	   (append ,(locflg_off (tr_dec (car l) (locflg_on))) %e))
   );end let
);end tr_local

;***************************************************************************
;*        TR_DECSEQ
;***************************************************************************
;*
;*DESCRIPTION: Translate a declaration sequence.
;*
;***************************************************************************
(de tr_decseq (l)
   (cond 
	((eq (length l) 1);single decl.
	   (tr_dec (car l) nil))
	(t 
	   (let ((fun%env fun%env));enclose fun%env in new scope  (used in lispfunpat)
		`((lambda (a)
		     (append 
			 ((lambda (%e) 
			      ,(let ((%p (append 
				(bvpat (car l) 
				    (ifn %loc_fundecs_flg t)) %p)))
	;if %loc_fundecs_flg=nil then the formal paramamter genfun_flg 
	;in bvpat is set to
	;nil, this means that a function name for each new function
	;declared in this sequence, has already been generated 
	;(indirectly via bvpat and lispfunpat) in tr_let or tr_local
	;if %loc_fundecs_flg=t then a new function name should be generated
	;(note: function name is a  generated unique symbol)
					(tr_decseq (cdr l))
			       );end let
		 	    );end lambda
			    (append a %e)
			   );end
			   a
		      );end append
		   );end lambda
		   ,(locflg_off (tr_dec (car l) (locflg_on)))
		  );end
	     );end let
	   );end t
   );end cond
);end tr_decseq

;***************************************************************************
;*        TR_DEC
;***************************************************************************
;*
;*DESCRIPTION: Translate a declaration.
;*
;***************************************************************************
(de tr_dec (dec x);note that x is a dummy to enable %loc_fundecs_flg to be
   (selectq (car dec) 		;turned on and off!
	((mk-type mk-datatype mk-infixr mk-infix mk-nonfix) nil)
	(mk-val `(list ,(tr_vb (cadr dec))))
	(mk-fun `(list ,(tr_fb (cadr dec))))
	(mk-abstype (tr_dec (caddr dec) nil))
	(mk-local (tr_local (cdr dec)))
	(mk-exception `(list ,(tr_eb (cadr dec))))
	(mk-decseq
	   (cond
	 	((cdr dec) (tr_decseq (cdr dec)))
		(t nil);empty sequence !
	   ));end cond
    );end selectq
);end tr_dec

;***************************************************************************
;*        TRAN
;***************************************************************************
;*
;*DESCRIPTION: Translate %pt into lisp code.
;*
;***************************************************************************
(de tran (p_tree)
   (setq new%%lb nil);structure of lisp symbols to hold ml values!
   (setq %compfns nil)
   (setq %loc_fundecs_flg nil)
   (optimize
	(prog1
	   (selectq (car p_tree)
		((mk-type mk-datatype mk-infixr mk-infix mk-nonfix) nil)
		((mk-val mk-fun mk-exception mk-local
		  mk-decseq mk-abstype)
		     (let ((bvs (bvpat p_tree t)))
		  	(setq new%%lb (build_lb (car p_tree) bvs))
			`(cons ',bvs ,(tr_dec p_tree nil))
		     ));end let
		 (t (tre p_tree))
	   );end selectq
	   (setq %compfns (nreverse (mapcar `optimize %compfns)))
	);end prog
    );end optimize
);end tran



;******************************************************************************
;initialize globals
(defconst lay '%lay)
(defconst val '%val)
(defconst ord '%ord)
(defconst rec '%rec)
(defconst record '%record)
(defconst exc '%exc)
(setq %ref nil)

;*****************************************************************************
; 	OPTIMIZE
;*****************************************************************************
;  These optimisation functions have been lifted from Old LCF with change:
;  (mk-fun mk-val mk-abstype mk-local) has replaced
;  (mk-let mk-letrec mk-abstype mk-absrectype)

(de optimize (code)
    (if (atom code) code
        (if (eq (car code) 'ap)
	    (optimize-ap code)
	    (trans-sexpr code))))		; optimize

; Unwind calls (f x y) where f is a curried function "\a. \b. body"
; call innermost function directly
; This optimization requires that closure functions be quoted with "quote"
;    instead of "function" -- it needs the function name and not just its
;    binding.  Using "quote" probably slows execution in some cases, but most
;    of them should be removed by this optimization.

(de optimize-ap (comb)
    (let ((code comb)(randstack nil)(lispfun)(env)(envcode))
; strip off and stack operands, find inner function
      (while (and (consp code) (eq (car code) 'ap))
	     (newl randstack (optimize (caddr code)))	; save rand
	     (setq code (cadr code)))		; look at rator
      (cond
	((and (atom code) (memq (car (explode-word code)) 
				'(mk-fun mk-val mk-abstype mk-local)))
; this is call to top-level ML function (not letref)
; macro-expand what "ap" would execute
	 (desetq (lispfun . env) (eval code))
; keep environment if there is one
	 (setq envcode (if env `(cdr ,code) nil))
	 (setq envcode
	       `(cons ,(nextl randstack) ,envcode))
	 (while (and randstack (get lispfun 'currybind))
		(setq lispfun (get lispfun 'currybind))
		(setq envcode
		      `(cons ,(nextl randstack) ,envcode)))
	 (setq code `(,lispfun ,envcode)))
	((and (consp code) (eq (car (explode-word (car code))) 'fun))
	 (desetq (lispfun  envcode) code)
	 (while (and randstack (get lispfun 'currybind))
		(setq lispfun (get lispfun 'currybind))
		(setq envcode
		      `(cons ,(nextl randstack) ,envcode)))
	 (setq code `(,lispfun ,envcode))))
; build up ordinary calls for remaining rands
      (while randstack
	     (setq code `(ap ,code ,(nextl randstack))))
      code))

; Map optimize over an S-expression, preserving its structure
; cannot use mapcar since not all S-expressions are lists
(de trans-sexpr (code)
    (if (atom code) code
        (cons (optimize (car code)) (trans-sexpr (cdr code))))) ;trans-sexpr

