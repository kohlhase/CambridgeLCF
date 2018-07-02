;***************************************************************************
;*
;*	S-macro
;*
;***************************************************************************
; S-macro	Macros for the LCF system
; Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile) (include llmac))

(eval-when (compile) (macros t))

(eval-when (compile load eval)
    ; expand a function call
    ;  (function f)    --->    (f arg1 ... argn)
    ;  others 	       --->    (funcall fun arg1 ... argn)
    (defun call-fun (fun args)
      (cond ((or (atom fun) (not (memq (car fun) '(function quote))))
	     `(funcall ,fun ,@args))
	    (t `(,(cadr fun) ,@args))))) ; call-fun

#-symbolics (defmacro first (x) `(car ,x))
#-symbolics (defmacro second (x) `(cadr ,x))
#-symbolics (defmacro third (x) `(caddr ,x))
#-symbolics (defmacro fourth (x) `(cadddr ,x))
#-symbolics (defmacro fifth (x) `(car (cddddr ,x)))

#-Multics
(df genprefix ignore nil)		; dummy genprefix (stupid Maclisp!)

;*****************************************************************************
;*	PTOKEN
;*****************************************************************************
; Print a constant string, computing length at compile-time
; for this use flatc rather than flatsize2, 
; since flatc is standard Franz while flatsize2 is flatc with a bug fixed
; the flatc bug concerns bignums, which do not concern this macro
(defmacro ptoken (str)
  `(pstringlen (quote ,str) ,(flatc str)))

;*****************************************************************************
;*	FAILWITH
;*****************************************************************************
;tok must be declared as exception (of type unit) use function defex (in dml)
(defmacro failwith (tok)
     `(throw (cons 'pac (cons ,tok nil)) 'evaluation)
);end

;*****************************************************************************
;*	COND-FAILWITH
;*****************************************************************************
; fail if any of the error messages are not nil
;tok must be declered as exception (of type string)  use function defexty (in 
; L-thyfns
(defmacro cond-failwith (tok . code)
    `(let ((msg (or . ,code)))
	(cond (msg 
            (throw (cons 'pac (cons ,tok msg)) 'evaluation)
	));end cond
   );end let
);end cond-failwith

;****************************************************************************
;*	MSG-FAILWITH
;*****************************************************************************
;tok must be declared as exception (of type string) use function defexty
; in L-dml
(defmacro msg-failwith (tok msg)
    `(throw (cons 'pac (cons ,tok ,msg)) 'evaluation)
);end
   

;*****************************************************************************
;*	FAILTRAP
;*****************************************************************************
; ML failure trapping :  trycode ?\tok failfun
(defmacro failtrap (failfun . trycode)
  (let ((x (gensym)))
    `((lambda (,x)
	(cond 
; test for package (removed test for atom 13/3/87) + caar x instead of car x
	 ((eq (car ,x) 'pac) ,(call-fun failfun (list `(cddar ,x))))
	 (t (car ,x))))
      #-symbolics (catch (list (progn . ,trycode)) evaluation)
      #+symbolics (*catch 'evaluation (list (progn . ,trycode)))
      )))					;failtrap
	     
;*****************************************************************************
;*	ERRTRAP
;*****************************************************************************
; Lisp error trapping 
(defmacro errortrap (errorfun . trycode)
   (let ((x (gensym)))
      `((lambda (,x)
	   (cond ; 
	        ((atom ,x) ,(call-fun errorfun (list x)))
	        (t (car ,x))))
	(errset (progn . ,trycode)))))	; errortrap

;*****************************************************************************
;*	EXISTS
;*****************************************************************************
; Apply the function to successive list elements
; and return the first non-nil value
; if none, return nil
(defmacro exists (fun . lists)
  (let ((vars (mapcar '(lambda (ignore) (gensym)) lists)))
   (let ((inits (mapcar '(lambda (v l) `(,v ,l (cdr ,v))) vars lists))
	 (args (mapcar '(lambda (v) `(car ,v)) vars)))
    `(do ,inits ((null ,(car vars)) nil)
	  (cond (,(call-fun fun args) (return (list ,@args))))))))   ; exists

;*****************************************************************************
;*	FORALL
;*****************************************************************************
(defmacro forall (fun . lists)
  (let ((vars (mapcar '(lambda (ignore) (gensym)) lists)))
   (let ((inits (mapcar '(lambda (v l) `(,v ,l (cdr ,v))) vars lists))
	 (args (mapcar '(lambda (v) `(car ,v)) vars)))
    `(do ,inits ((null ,(car vars)) t)
	  (cond (,(call-fun fun args)) ((return nil)))))))  ; forall

;*****************************************************************************
;*	DML
;*****************************************************************************
(defmacro dml (ml-fn n lisp-fn mty)
  `(declare-ml-fun (quote ,ml-fn) (quote ,n) (quote ,lisp-fn) (quote ,mty))) ; dml

;*****************************************************************************
;*	DMLC
;*****************************************************************************
(defmacro dmlc (id exp mty)
  `(declare-ml-const (quote ,id) (quote ,exp) (quote ,mty))) ; dmlc


;***************************************************************************
;*	DE
;****************************************************************************
(defmacro de (name larg . body)
  (cons 'defun
	(cons name
	      (cons larg
		    (cond
		      ((or (not (atom larg)) (null larg))
		       body)
		      (t (cons ['setq larg ['listify larg]] body)))))))	;de
