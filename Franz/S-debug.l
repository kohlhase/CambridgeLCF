;******************************************************************
;*	debug
;*****************************************************************
; set of useful debugging functions accessable from ML:
;
; lisptrace : string -> unit ;traces corresponding lispfunction
;			uses lisp tracer package.
; lispfun : string -> unit ;prints corresponding lisp function
;		(if it is not compiled).
; funlisp : string -> string ;input is lispfunction, returns ML function
;

(dml |lisptrace| 1 lisptrace (mk-funtyp (string) (mk-recordtyp)))
(dml |lispfun| 1 lispfun (mk-funtyp (string) (mk-recordtyp)))
(dml |funlisp| 1 funlisp (mk-funtyp (string) (string)))


(defun sym_to_fun (f) 
  (prog (la lb)
; lisp can only cope with a very limited number of recursive function
; calls, hence the need for hacking below:
	(setq la (div_two global%env))
	(setq lb (div_two (car la)) lc (div_two (cdr la)))
;	(setq ld (div_two (car lb)) le (div_two (cdr lb)))
;	(setq lf (div_two (car lc)) lg (div_two (cdr lc)))
loop
      (return
	(cond
	    ((funlisp f (car lb)))
	    ((funlisp f (cdr lc)))
	    ((funlisp f (car lb)))
	    ((funlisp f (cdr lc)))
	    (t 
		(llprinc 
		 (concat
		    f
		   '| not found in env, trying |
		   (setq f (decrease_last f))			
		   '| instead; |
	         ))
		(llterpri)
	        (go loop))))))

(defun funlisp (x) (funlispa x global%env))
(defun funlispa (x l)
  (let ((sym (eval (cadar l))))
   (cond
        ((null l) nil)
	((and (listp sym) (equal (car sym) x))
		(concat (caar l)))
	(t (funlispa x (cdr l))))))

(defun div_two (l) (div_twoo nil l (/ (length l) 2)))

(defun div_twoo (l1 l2  n)
   (cond
	((< (length l2) n) `(,l1 . ,l2))
	(t 
	   (div_twoo (cons (car l2) l1) (cdr l2) n))))

(defun decrease_last (f)
   (let ((l (explode f)))
	(let ((l1 (firsts l '())) (l2 (last l)))
	   (let 
	    ((new (ncons (concat (- (- (cascii (car l2)) (cascii '|0|)) 1)))))
	    (implode (append l1 new))))))

(defun firsts (l1 l2)
   (cond
	((eq 1 (length l1)) l2)
	(t (firsts (cdr l1) (append l2  `(,(car l1)))))
   ))


;**************************************************************
; display corresponding lisp function
; input: ML functio name
; side effect: lisp function printed 
(de lispfun (f)
   (let ((code `(pp ,(car (eval (get_val_binding f))))))
	(eval code) (llterpri)
   );end let
);end lispfun

; input: ML function name
; result: trace corresponding lispfunction
(de lisptrace (f)
   (let ((code `(trace ,(car (eval (get_val_binding f))))))
      (eval code) (llterpri)
   );end let
);end




