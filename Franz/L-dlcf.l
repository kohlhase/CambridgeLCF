;******************************************************************************
;*
;*	DLCF
;*
;*******************************************************************************
; define exceptions,types and functions for LCF.
; Origin: EDINBURGH LCF (Milner,Gordon,Wadsworth...) 
; Modified: CAMBRIDGE LCF (Huet,Paulson,Cousineau...) 
; Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile)
  (include llmac)
  (include S-macro)
  (include S-constants)
  (*lexpr concat)
  (genprefix dml)  
);end eval-compile

;******************************************************************************
; EXCEPTIONS (defex declared in DML)
; The following exceptions are used in LCF:
; We declare them in lisp so that the unique symbols that represents the 
; the exceptions will be the same as the exception itself!
; Useful when matching exceptions in lisp.
;	theory : string
;	rule : string * thm list
; Note: type goal is not repr. by (goal)  in lisp. Hence, exception tactic must
; be declared in ML.
;	tactic : string * goal list
;	general : string (declared in S-dml.l)

(defexty '|theory| '(string))
(defexty '|syntax| '(string))
(defexty '|rule| '(mk-tupletyp (string) (list (thm))))




;******************************************************************************
; TYPES (pretycon declared in DML)

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


;define goal
(putprop 'goal 0 'arity)
(putprop 'goal '(mk-tupletyp (list (form)) (form)) 'abbrevtyp)
(putprop 'goal '() 'tyvarl)
(putprop 'goal 'goal 'tyname)

; LCF stuff
(dml |ml_curried_infix| 1 ml-curried_infix (mk-funtyp (string) (mk-recordtyp)))

(de ml-curried_infix (str)
   (cond
	((memq str res_words)
	   (msg-failwith '|general|
	       (concat str '| cannot be curried-infixed|)))
	(t 
	   (putprop str 560 prec_lev);global precedence
	   (putprop str `(mlcinf-rtn ',str) lang2)); associated code
   );end cond
);end 

(de mlcinf-rtn (x)
	`(mk-appn (mk-appn (mk-var ,x) ,par_res) ,(parse 560)))


(defconst exfix-sym '$)

(de exfix-rtn ()
	(gnt)
	`(mk-var ,(if (is-stringconst ptoken) (cdr ptoken) ptoken)))

(unop exfix-sym '(exfix-rtn))
