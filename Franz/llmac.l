;;; -*- Mode: LISP; Base: 10;; Package: USER -*-

; llmac.lisp   Macros de traduction LeLisp -> Maclisp,Zetalisp
;                   Origine JER & JMH  Mars 82.
;                   Modifie 24/3/82  GH
;                   Modifie 8/16/84  Maurice

; IMPORTANT!
; changed decr, incr, and when to use cond instead of if
; decr did not work because "if" was undefined for it
; the manifestation of this bug was most obscure.

; changed selectq-aux to generate memq rather than member.

#+symbolics (macro macros (ignore) nil)
#+symbolics (macro %include (ignore) nil)
#+symbolics (macro include (ignore) nil)
 
(eval-when (compile)  
#-symbolics  (macros t)	
  (*lexpr concat uconcat catenate)
  (special ~~l))

(eval-when (compile load eval)
  #+unix
  (defun selectq-aux (clause)
    (cond
      ((memq (car clause) '(t otherwise))
       (cons 't (cdr clause)))
      ((atom (car clause))
       (cons (list 'eq ~~l (list 'quote (car clause))) (cdr clause)))
      (t (cons (list 'memq ~~l (list 'quote (car clause)))
	       (cdr clause)))))			;selectq-aux
  
  (defun croch-ouvr ()
    (let ((l ) (lu ))
      (do () (nil)
	(setq lu (read))
	(cond ((eq lu '|]|)(return (cons 'list (nreverse l))))
	      (t (setq l (cons lu l)))))))	;croch-ouvr
  
  ;(defun barre ()
  ;  (let ((lchar nil)(char nil))
  ;    (do () (nil)				; forever
;	(setq char (tyi))
;	(cond ((eq char 124)			; "|"
;	       (cond ((eq (tyipeek) 124)(tyi))	; || for "|"
;		     (t (return (implode (nreverse lchar))))
;		     )))
;	(setq lchar (cons char lchar)))))	;barre
  
  (defun croch-ferm () '|]|)			;croch-ferm
  
  (setsyntax '|[| 'macro 'croch-ouvr)		;for abstract syntax
  (setsyntax '|]| 'macro 'croch-ferm)
;  (setsyntax (ascii 124) 'macro 'barre)		; n

); end eval-when
;;;          Les macros de definition.


(defmacro df (name arg . body)
  `(defun ,name fexpr (,arg) ,@body))		;df

(defmacro dm (name arg . body)
  `(defun ,name macro (,arg) ,@body))		;dm

(defmacro dmd (name larg . body)
  `(defun ,name macro ,larg (displace ,(car larg) (progn ,@body))))	;dmd

(defmacro dmc (char larg . body)
  `(setsyntax ,char (quote macro) (quote (lambda ,larg ,@body))))	;dmc

;;;          Toutes les autres

#+Multics
(defmacro consp (x)
  ['eq ['typep x] ['quote 'list]])		;consp

(defmacro decr (var #+Symbolics &optional val)
  ['setq var (cond ((null val) ['1- var]) (t ['- var val]))])	;decr

#-(or symbolics lelisp)
(defmacro defvar (x y)
  `(setq ,x ,y))				;defvar

#-symbolics
(defmacro defconst (x y)
  `(setq ,x ,y))				;defconst

#-(or symbolics franz)
(defmacro evenp (x)
  `(not (oddp ,x)))				;evenp

#-symbolics
(defmacro *exit (name . body)
  `(throw (progn ,@body) ,name))		;exit

#+symbolics
(defmacro exit (name . body)
  `(*throw ',name (progn ,@body)))		;exit
;****************************
(defmacro addr (x y)
	`(setq ,x
		(append ,y ,x)
	);end setq
);end addr

;transform oml duples to sml tuples (for returned values of lcf functions)
(defmacro dupl_tupl (d)
   `(list (car ,d) (cdr ,d))
);

;transform sml tuples to oml duples (for argumants to lcf functions)
(defmacro tupl_dupl (tu)
   `(cons (car ,tu) (cadr ,tu))
);end

(defmacro dupl_tupl_l (l)
  `(mapcar 'dupl_tupl ,l)
);end

#-symbolics
(defmacro if (test then . else)
  `(cond (,test ,then) (t nil ,@else)))		;if

(defmacro ifn (test then . else)
  `(cond ((not ,test) ,then) (t nil ,@else)))	;ifn

(defmacro incr (var #+Symbolics &optional val)
  ['setq var (cond ((null val) ['1+ var]) (t ['+ var val]))])	;incr

(defmacro let-named (name desc . body)
  (cons ['label name
	(cons 'lambda (cons (mapcar 'car desc) body))]
	(mapcar 'cadr desc)))			;let-named

#+Multics
(defmacro listp (x)
  ['or ['null x] ['eq ['typep x] ['quote 'list]]])	;listp

#-symbolics
(defmacro logand (x y)
  ['boole 1 x y])				;logand

(defmacro logor (x y)
  ['boole 7 x y])				;logor

(defmacro logshift (x y)
  ['lsh x y])					;logshift

#-symbolics
(defmacro logxor (x y)
  ['boole 6 x y])				;logxor

(defmacro mcons l
  ['cons (car l)
  (cond ((null (cddr l)) (cadr l)) (t (cons 'mcons (cdr l))))])	;mcons

#-symbolics
(defmacro neq (x y)
  ['null ['eq x y]])				;neq

(defmacro nconc1 (l a)
  ['nconc l ['list a]])				;nconc1

(defmacro nextl (var)
  ['prog1 ['car var] ['setq var ['cdr var]]])	;nextl

(defmacro newl (var val)
  `(setq ,var (cons ,val ,var)))		;newl

(defmacro newr (var val)
  `(setq ,var (cond (,var (nconc1 ,var ,val))
		    (t (list ,val)))))		;newr

#+Multics
(defmacro oblist ()
  '(delq () (flat (makoblist ()))))		;oblist

(defmacro repeat (count . body)
  (let ((~l  (gensym)))
    `(do ,~l ,count (1- ,~l) (<= ,~l 0) ,@body)))	;repeat

#-symbolics
(defmacro selectq (sel . lclauses)
  (let ((~~l (gensym)))
    ['let [[~~l sel]]
    (cons 'cond (mapcar 'selectq-aux lclauses))]))	;selectq

#+franz
(defmacro synonymq (sym1 sym2)
  `(putd ',sym1 (getd ',sym2)))			;synonymq

#-symbolics
(defmacro tag (name . body)
  `(catch (progn ,@body) ,name))		;tag

#+symbolics
(defmacro tag (name . body)
  `(*catch ',name (progn ,@body)))		;tag

#-symbolics
(defmacro unless (test . body)
  `(cond (,test nil)(t ,@body)))		;unless

(defmacro until (test . body)
  `(prog ()
      *etiq* (let ((val ,test))
	       (cond (val (return val))
		     (t ,@body
			(go *etiq*))))))	;until
; Note: the let avoids double evaluation of test  on exit.
; This will give compiler warnings in Franz compiler, since the go and
; the return are non local.

#-symbolics
(defmacro when (test . body)
  `(cond (,test ,@body)))			;when

(defmacro while (test . body)
  `(prog ()
      *etiq* (cond (,test ,@body (go *etiq*))
		   (t (return nil)))))		;while

(defmacro <>0 (x)
  ['not ['zerop x]])				;<>0

#-symbolics
(defmacro <= (x y)
  `(not (greaterp ,x ,y)))			; <=

#-symbolics
(defmacro >= (x y)
  `(not (lessp ,x ,y)))				; >=

#+symbolics
(progn
  (remob 'df 'lmfs)
  (mapcar #'globalize
	  '(de
	    df
	    dm
	    dmd
	    dmc
	    croch-ouv
	    croch-ferm
	    barre
	    decr
	    exit
	    ifn
	    incr
	    let-named
	    logor
	    logshift
	    mcons
	    nconc1
	    nextl
	    newl
	    newr
	    repeat
	    tag
	    until
	    while
	    <>0
	    macros
	    %include
	    include)))

