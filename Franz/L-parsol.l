;*****************************************************************************
;*
;*	PARSOL
;*
;*****************************************************************************
;Original: F-parsol (Cambridge LCF)
;Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)

; When changing precedences you must update every call to parse.
; There are many interactions among the precedences of the operators.

; note that the "optr" arg of term-rtn and form-rtn is not used.
; thus syntax error messages do not mention the specific operator or
; connective being parsed.  Earlier code consed up error message that
; usually were not needed, wasting storage.  A better way to make
; specific error messages would be to make term-check and form-check
; take args msg1, msg2, and msg3 -- which would be concatenated only
; if an error actually occurred.  
;  - LP

(eval-when (compile)
  (include S-constants)
  (include llmac)
  (include S-macro)
  (genprefix parsol))

(defconst prec_lev 'ollp); set for the definitions in this file
(defconst endcnrtok '|`|)
(defconst exfix_sym '|op|)

(defconst spec-toks
    '(|\\|  ||||  |:|  |(|  |)|  |^|  |=>|  |,|  |.|
      |==|  |<<|  |~|  |/\\|  |\\/|  |==>|  |<=>|  |?|  |!|  |`| ))

(defconst anticnr-tok '|^|)
(defconst condl-tok '|=>|)
(defconst else-tok '|\||)
(defconst lambda-tok '|\\|)
(defconst eq-tok '|==|)
(defconst ineq-tok '|<<|)
(defconst neg-tok '|~|)
(defconst conj-tok '|/\\|)
(defconst disj-tok '|\\/|)
(defconst imp-tok '|==>|)
(defconst iff-tok '|<=>|)
(defconst forall-tok '|!|)
(defconst exists-tok '|?|)
(defconst arrow-tok '|->|)
(defconst sum-tok '|+|)
(defconst prod-tok '|*|)

(de vartype-rtn ()
    (prog (n)
	  (if cflag (return mul_sym))
	  (setq n 1)
    loop  (ifn (or (numberp token) (eq toktyp 1) (eq token mul_sym))
	       (return (imploden (iterate multiply n))))
	  (gnt)
	  (when (and (eq ptoken mul_sym) (not cflag))
	    (setq n (add1 n))
	    (go loop))
	  (return (imploden (nconc (iterate multiply n) (exploden ptoken))))
	  ))					;vartype-rtn


; parse an OL quotation (for ML)
(defun parse-ol ()
   (let ((lang1 'ol1) (lang2 'ol2) (prec_lev 'ollp) (atom_rtn '(ol-atomr))
         (juxt_lev 120)	; precedence of application
	 (%mk=antiquot 'MK=ANTIQUOT)
	 (juxt_rtn '(oljuxt par_res)) (ibase 10) (parsedepth 0))
      (parse 0)
      ; this check catches dangling predicate symbols
      (if (or (memq (car par_res) term-constrs)
	      (memq (car par_res) form-constrs))
	  par_res
	  (parse_failed "OL: syntax error in quotation"))
   ))  ;parse-ol

; declare a user-defined OL infix
; called from theory package
(defun olinfix (x typ)
 (let ((lang1 'ol1)(lang2 'ol2)(prec_lev 'ollp))
    (putprop x typ 'olinfix)
    (binop x (+ olinprec 5)	; right-associative
       (list (if (eq typ 'paired) 'olinf-rtn 'olcinf-rtn) (list 'quote x)))
 ))  ;olinfix

; parse paired OL infix
(defun olinf-rtn (x)
  (list 'MK=COMB
    (mk-ol-atom x)
    (list 'MK=PAIR
	(term-check par_res "par_res of infix must be a term")
	(term-check (parse olinprec) "arg2 of infix must be a term")))
 )  ;olinf-rtn

; parse curried OL infix
(defun olcinf-rtn (x)
    (list 'MK=COMB
	(list 'MK=COMB
	      (mk-ol-atom x)
	      (term-check par_res "par_res of infix must be a term"))
	(term-check (parse olinprec)
           "arg2 of infix must be a term")))  ;olcinf-rtn

; handle parentheses, also special token ()
(defun lpar-rtn ()
   (cond ((eq token rparen_sym) (gnt) '(MK=CONST |()|))
	(t 
	  (prog1
		(parse 0)
		(ifn (eq token rparen_sym)
		   (parse_failed '|OL: missing left paranthesis|)
		   (gnt)
		);end ifn
	   ));end prog1
   );end cond
)  ;lpar-rtn

; logical connectives
(defun form-rtn (optr constr a b)
    optr					;not used
    (list constr
      (form-check a "OL: fst arg of connective must be a formula")
      (form-check b "OL: snd arg of connective must be a formula")))  ;form-rtn

; check that an object is a form, print msg if not
(defun form-check (ob msg)
  (if (memq (car ob) form-constrs) ob (parse_failed 
	(concat '|OL: | msg))))  ;form-check

; routine for OL atoms, linked to atom-rtn
(defun ol-atomr () (mk-ol-atom ptoken))  ;ol-atomr

; determine the use of an OL atom : constant or variable
; for OL, numbers are scanned as symbols
(defun mk-ol-atom (x)
   (cond ((memq x spec-toks)  (parse_failed (concat "OL: " x " cannot be a term")))
	((constp x)  (list 'MK=CONST x))
	((predicatep x)  (list 'MK=PREDSYM x))
	(t (list 'MK=VAR x))))  ;mk-ol-atom

; routine for juxtaposed OL objects, linked to juxt-rtn
; handles predicates and combinations
(defun oljuxt (x)
  (if (eq (car x) 'MK=PREDSYM)
    (list 'MK=PREDICATE (cadr x)
      (term-check (parse juxt_lev)
	   "argument of predicate must be a term"))
    (list 'MK=COMB
      (term-check x "formula terminated by junk")
      (term-check (parse juxt_lev)
	   "term juxtaposed with formula")))
 )  ;oljuxt

; Parse lambda or quantifier
(defun lamq-rtn (constr chk n msg)
 (let ((x (cond ((eq token anticnr-tok) (gnt) (metacall))
	      ((not (equal toktyp 1))
	       (parse_failed (concat "OL: " token " in a prefix")))
	      (t (gnt) (mk-ol-atom ptoken)))))
    (while (eq token colon_sym) (gnt) (setq x (list 'MK=TYPED x (olt))))
    (list constr x
      (cond ((eq token period_sym) (gnt) (funcall chk (parse n) msg))
	    (t (lamq-rtn constr chk n msg))))
))  ;lamq-rtn

(defun lam-rtn ()
  (lamq-rtn 'MK=ABS (function term-check) 70
	 "lambda body must be a term"))  ;lam-rtn

(defun quant-rtn (constr)
  (lamq-rtn constr (function form-check) 5
	 "can only quantify a formula"))  ;quant-rtn

; negation -- extends over predicates only
(defun neg-rtn ()
  (list 'MK=NEG
    (form-check (parse 59) "can only negate a formula"))) ; neg-rtn


; infix operators on terms (comma, ==, <<)
(defun term-rtn (optr constr a b)
   optr						;not used
   (list constr
     (term-check a "par_res of operator must be a term")
     (term-check b "arg2 of operator must be a term"))) ;term-rtn

; check that an object is a term, fail if not
(defun term-check (ob msg)
  (if (memq (car ob) term-constrs) ob (parse_failed 
	(concat '|OL: |msg))))  ;term-check

(defun condl-rtn (p)
  (list 'MK=COND
        (term-check p "condition of conditional not term")
        (term-check 
		(prog1
		   (parse 80)
		   (ifn (eq token else-tok)
			(parse_failed 
		    '|OL: need snd branch to conditional|)
			 (gnt)
		   );end ifn
		);end prog
	       "1 st branch of conditional not term")
        (term-check (parse 80) "2 nd branch of conditional not term")
))  ;condl-rtn


; antiquotation of terms/forms (MK=ANTIQUOT) or types (MK=TYPE=ANTIQUOT)
(defun metacall ()
  (list	%mk=antiquot
     (progn (gnt)
       (cond ((eq ptoken lparen_sym)
		(prog1
		   (parse_ml metaprec)
		   (ifn (eq token rparen_sym)
			(parse_failed '|OL: bad antiquotation|)
			(gnt)
		   );end ifn
		));end prog1
	     ((eq ptoktyp 1) (mlatomr))
	     ((parse_failed "OL: junk in antiquotation"))))))  ;metacall

; type constraint on term
(defun oltyp-rtn ()
  (list	'MK=TYPED
	(term-check par_res "only a term can have a type")
	(olt)))  ;oltyp-rtn


; free-standing type quotation
; this is presumably a separate recursive descent parser
(defun olt ()
  (let ((lang1 'ol1) (%mk=antiquot 'MK=TYPE=ANTIQUOT))
    (olt1 (olt2 (olt3 (olt4))))))  ;olt

(defun olt1 (x)
  (cond ((eq token arrow-tok) (gnt) (list 'MK=TYPE '|fun| x (olt)))
	(t x)))  ;olt1

; PPLAMBDA does not have any built-in "sum" type, but user may define it
(defun olt2 (x)
  (cond ((eq token sum-tok) (gnt)
           (list 'MK=TYPE '|sum| x (olt2 (olt3 (olt4)))))
	(t x)))  ;olt2

(defun olt3 (x)
  (cond ((eq token prod-tok) (gnt) (list 'MK=TYPE '|prod| x (olt3 (olt4))))
	(t x)))  ;olt3

(defun olt4 ()
  (prog	(x)
    (gnt)
    (when (eq ptoken lparen_sym)
     (setq x (cond ((eq token rparen_sym) (gnt) nil) (t (olt5))))
     (go l))
    (setq x (list
	    (cond ((eq ptoken anticnr-tok) (metacall))
; type variables now as in SML (2/2/87)
;		  ((eq (car (explode ptoken)) mul_sym)
		  ((is_type_var ptoken)
		   (list 'MK=VARTYPE ptoken))
		  ((not (eq ptoktyp 1))
		   (parse_failed
		     (concat "OL: " ptoken " is not allowed in a type")))
		  (t (list 'MK=TYPE ptoken)))))
 l  (cond ((eq toktyp 1) (gnt))
	  ((eq (length x) 1) (return (car x)))
	  (t (parse_failed "OL: missing type constructor")))
  (setq x (list (cons 'MK=TYPE (cons ptoken x))))
  (go l)))  ;olt4

(defun olt5 ()
  (prog	(x)
	(setq x (list (olt)))
   loop	(cond ((eq token rparen_sym) (gnt) (return x))
	      ((eq token comma_sym) (gnt) (setq x (append x (list (olt))))
			    (go loop))
	      (t (parse_failed "OL: missing separator or terminator in type")))
))  ;olt5


; set up OL symbols and precedences
(let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))

  (putprop endcnrtok 0 'ollp)
  (putprop rparen_sym 0 'ollp)
  (unop lparen_sym '(lpar-rtn))
  (unop forall-tok '(quant-rtn 'MK=FORALL))
  (unop exists-tok '(quant-rtn 'MK=EXISTS))
  (unop neg-tok '(neg-rtn))

  ; in OL, all infixes associate to RIGHT
  ; however == and << do not associate at all

; the first arg of form-rtn should be a string (for error messages)
; however it is currently unused

  (binop iff-tok 25 '(form-rtn 'if-and-only-if 'MK=IFF par_res (parse 20)))
  (binop imp-tok 35 '(form-rtn 'implication 'MK=IMP par_res (parse 30)))
  (binop disj-tok 45 '(form-rtn 'disjunction 'MK=DISJ par_res (parse 40)))
  (binop conj-tok 55 '(form-rtn 'conjunction 'MK=CONJ par_res (parse 50)))
  (binop eq-tok 60 '(term-rtn 'equality 'MK=EQUIV par_res (parse 60)))
  (binop ineq-tok 60 '(term-rtn 'inequality 'MK=INEQUIV par_res (parse 60)))
  (binop condl-tok 85 '(condl-rtn par_res))
  (binop comma_sym 95 '(term-rtn 'tupling 'MK=PAIR par_res (parse 90)))
  (unop lambda-tok '(lam-rtn))

  (putprop else-tok 10 'ollp)	; the value of the number seems irrelevant

  (binop colon_sym 105 '(oltyp-rtn))
  (unop anticnr-tok '(metacall))
  (unop exfix_sym '(progn (gnt) (mk-ol-atom ptoken)))
 )

(setq olinprec 100)


(setq term-constrs '(MK=ANTIQUOT MK=CONST MK=VAR MK=COMB MK=PAIR MK=ABS
                    MK=COND MK=TYPED))

(setq form-constrs '(MK=ANTIQUOT MK=PREDICATE
		    MK=EQUIV MK=INEQUIV MK=NEG MK=CONJ MK=DISJ
		    MK=IMP MK=IFF MK=FORALL MK=EXISTS))


(setq metaprec 20)
(setq prec_lev 'mllp)
