;***************************************************************************
;*
;*	WRITOL
;*
;***************************************************************************
; print ol-objects
; Original: F-writol  (Cambridge LCF)
; Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)


(eval-when (compile)
  (include S-constants)
  (include llmac)
  (include S-macro)
  (include L-ol-rec)
  (genprefix typeol))

(defvar %printtypes nil)

(dml |show_types| 1 ml-show_types (mk-funtyp (bool) (bool)))
(de ml-show_types (b) (setq %printtypes b))  ;ml-show_types

(dml |print_term| 1 ml-print_term (mk-funtyp (term) (mk-recordtyp)))

(de ml-print_term (tm)
    (ptoken |`|)
    (print-tm (prep-tm tm) t t)
    (ptoken |`|)
    )  ;ml-print_term

(dml |print_form| 1 ml-print_form (mk-funtyp (form) (mk-recordtyp)))

(de ml-print_form (w)
    (ptoken |`|)
    (print-fm (prep-fm w) t)
    (ptoken |`|)
    )  ;ml-print_form


(dml |print_thm| 1 ml-print_thm (mk-funtyp (thm) (mk-recordtyp)))

(de ml-print_thm (th)
  (mapc '(lambda (x) x (ptoken |.|)) (car th))
  (ptoken |\|-|) 
  (ml-print_form (cadr th))
  )  ;ml-print_thm


(dml |print_type| 1 ml-print_type (mk-funtyp (type) (mk-recordtyp)))

(de ml-print_type (ty)
  (ptoken |`:|)
  (print-ty ty t)
  (ptoken |`|)
  )  ;ml-print_type


; precedence information for when to print brackets
; the left symbol binds more tightly than the right symbols
; associativity logic is not stored here, but included in printing functions
; the symbols include those introduced by prep-tm/fm

(mapc '(lambda (x) (putprop (car x) (cdr x) 'closes))
      '((neg . (forall exists conj disj imp iff))
        (conj . (forall exists conj disj imp iff))
	(disj . (forall exists disj imp iff))
	(imp . (forall exists imp iff))
	(iff . (forall exists iff))
	(pair . nil)
	(then . (then))
	(else . (abs then))
	(listcomb . (abs listcomb infixcomb then typed))
	(infixcomb . (abs listcomb infixcomb then typed))
	(typed . (infixcomb))
	(|fun| . (|fun|))
	(|sum| . (|sum| |fun|))
	(|prod| . (|prod| |sum| |fun|))
 ))


; are parens needed around "X op2 Y" if a neighboring infix is op1?
(de closes (op1 op2) (memq op2 (get op1 'closes)))  ;closes


; preprocessed terms may have the form (class . (term-list . type))
; the type must be in the same position as types in terms
; this macro gets the term-list in the middle
(defmacro get-term-list (tm) `(cadr ,tm))

(defmacro make-prep-term (class term-list type)
    `(cons ,class (cons ,term-list ,type)))


; preprocessed formulas are simply lists (class arg1 ... argn)


; prepare pairs for printing
; put the combination ((PAIR X) Y) into a special format
(de prep-pair (rator rand ty)
 (if (and (is-comb rator)
	  (eq (get-const-name (get-rator rator)) 'PAIR))
     (make-prep-term 'pair 
	 (list (prep-tm (get-rand rator)) (prep-tm rand))
	 ty))
 )  ;prep-pair


; prepare conditional for printing
; put the combination (((COND P) X) Y) into a special format
(de prep-cond (rator rand ty)
 (if (is-comb rator)
   (let ((ratrat (get-rator rator)))
     (if (is-comb ratrat)
       (let ((ratratrat (get-rator ratrat)))
	 (if (and (is-const ratratrat)
		  (eq (get-const-name ratratrat) 'COND))
	   (make-prep-term 'cond
	     (list (prep-tm (get-rand ratrat))
		   (prep-tm (get-rand rator))
		   (prep-tm rand))
	     ty)))))))		; prep-cond


; detect infixes and long combinations
(de prep-comb (rator rand ty)
  (let ((prator (prep-tm rator))(prand (prep-tm rand)))
     (cond
     ((and (is-const prator)
	   (eq (get (get-const-name prator) 'olinfix) 'paired)
	   (eq (term-class prand) 'pair))
      (make-prep-term 'infixcomb (cons prator (get-term-list prand)) ty))
     ((eq (term-class prator) 'listcomb)
      (prep-curr (get-term-list prator) prand ty))
     ((make-prep-term 'listcomb (list prator prand) ty)))
     ))  ;prep-comb


; see if ((tm1 tm2 ...) y) is the curried infix "tm2 <tm1> y"
; otherwise return (tm1 tm2 ... y)
(de prep-curr (tml y ty)
      (let (((tm1 tm2 . tmtail) tml))
	(if (and (null tmtail) (is-const tm1)
		 (eq (get (get-const-name tm1) 'olinfix) 'curried))
	    (make-prep-term 'infixcomb (list tm1 tm2 y) ty)
	    (make-prep-term 'listcomb (append tml (list y)) ty)
	    )))					;prep-curr

; preprocess a term for easier printing
; locate all conditionals, pairs, infixes, and long combinations
(de prep-tm (tm)
  (selectq (term-class tm)
     ((var const) tm)
     (abs (make-abs (get-abs-var tm)(prep-tm (get-abs-body tm))
	      (get-type tm)))
     (comb (let ((rator (get-rator tm))
		 (rand (get-rand tm))
		 (ty (get-type tm)))
	     (or (prep-pair rator rand ty)
		 (prep-cond rator rand ty)
		 (prep-comb rator rand ty))))
     (t (lcferror 'prep-tm)))
  )  ;prep-tm


; preprocess a formula
(de prep-fm (fm)
 (selectq (form-class fm)
  (pred (prep-pred-form (get-pred-sym fm) (prep-tm (get-pred-arg fm))))
  ((conj disj imp iff)
   (prep-conn-form (get-conn fm)
	 (prep-fm(get-left-form fm)) (prep-fm(get-right-form fm))))
  ((forall exists)
   (make-quant-form (get-quant fm)
	 (get-quant-var fm) (prep-fm(get-quant-body fm))))
  (t (lcferror 'prep-fm))
))  ;prep-fm


; re-build a predicate, changing equiv(x,y) to x==y, likewise for inequiv
(de prep-pred-form (sym arg)
    (if (and (memq sym '(|equiv| |inequiv|))
	     (eq 'pair (term-class arg)))
	(cons 'infixpred (cons sym (get-term-list arg)))
	(make-pred-form sym arg))
 )   ; prep-pred-form


; re-build a connective formula, changing A ==> FALSITY()  to  ~A
(de prep-conn-form (conn left right)
    (if (and (eq 'imp conn)
	     (eq 'pred (form-class right))
	     (eq 'FALSITY (get-pred-sym right)))
	(list 'neg left)
	(make-conn-form conn left right)
 ))  ; prep-conn-form


; is the OL type polymorphic?
(de opoly (ty)
   (or (is-vartype ty) (exists 'opoly (get-type-args ty))))  ;opoly


; print a term
; op1 is the operator that will be printed before or after
;     for deciding whether to print disambiguating parentheses
; needty tells print-tm to print enough type information to deduce the
;    type of this term, perhaps from the types of its subterms
; method for minimizing types that are printed:
;    for long combinations whose rator is a polymorphic constant,
;    print types of result and operands, but not type of constant
; Without optimization, redundant types would cause an exponential amount
;    of printing.
(de print-tm (tm op1 needty)
 (let ((op2 (term-class tm))
       (tml (get-term-list tm))
       (ty (get-type tm)))
  (let ((pcrator 		; is rator a polymorphic constant?
	  (and %printtypes
	       (memq op2 '(listcomb infixcomb))
	       (let ((r (first tml)))	 ; find innermost operator
		 (if (eq (term-class r) 'infixcomb)
		     (setq r (first (get-term-list r))))
	         (and (is-const r) (opoly (constp (get-const-name r))))))))
    (let ((tyflag 		; print type of this particular term?
            (and needty %printtypes
		 (selectq op2
		   (var t)
		   (const (opoly (constp (get-const-name tm))))
		   ((listcomb infixcomb) pcrator)
		   (t nil)))))
      ; possibly one pair of parens for precedence, another for typing
      (let ((cl1 (closes op1 (if tyflag 'typed op2)))
	    (cl2 (and tyflag (closes 'typed op2))))
       (if cl1 (ptoken |(|))
       (if cl2 (ptoken |(|))
       (pbegin 0)
       (selectq op2
	(var (pstring (get-var-name tm)))
	(const (print-const (get-const-name tm)))
	(abs (print-abs tm needty))
	(cond (print-cond tml needty))
	(pair (ptoken |(|) (print-pair tm needty)(ptoken |)|))
	(listcomb (print-listcomb tml pcrator))
	(infixcomb (print-infixcomb tml pcrator))
	(t (lcferror 'print-tm)))
       (cond (tyflag		; print type
	    (if cl2 (ptoken |)|)
		    (ifn (memq op2 '(var const)) (ptoken | |)))
	    (pbreak 0 0)
	    (ptoken |:|) (print-ty ty t)))
       (if cl1 (ptoken |)|))
       (pend))))))  ;print-tm


; print a constant (may be infix standing alone)
(de print-const (name)
    (if (get name 'olinfix) (ptoken |op |))
    (pstring name))		; print-const


; print an abstraction
(de print-abs (tm needty)
    (ptoken |\\|)		; i.e. lambda
    (print-tm (get-abs-var tm) 'abs nil)
    (ptoken |.|)
    (pbreak 0 0)
    (print-tm (get-abs-body tm) 'abs needty))	; print-abs


; print a conditional
(de print-cond (tml needty)
     (ptoken |(|)
     (print-tm (first tml) 'then nil)
     (ptoken | => |)
     (pbreak 0 1)
     (print-tm (second tml) 'else nil)
     (ptoken | \| |)		; vertical bar
     (pbreak 0 1)
     (print-tm (third tml) 'else needty)
     (ptoken |)|))		; print-cond


; print a pair or n-tuple, suppressing parentheses using associativity
(de print-pair (tm needty)
    (while (eq 'pair (term-class tm))
	   (print-tm (first (get-term-list tm)) 'pair needty)
	   (ptoken |,|) (pbreak 0 0)
	   (setq tm (second (get-term-list tm))))
    (print-tm tm 'pair needty))	; print-pair


; print a long combination (f x1 ... xn)
(de print-listcomb (tml pcrator)
  (let ((y (nextl tml)) (prev nil))
   (print-tm y 'listcomb (not pcrator))
   (while tml
     (setq prev y) (setq y (nextl tml))
     (if (and(memq (term-class prev) '(var const))
	     (memq (term-class y)    '(var const)))
	 (ptoken | |))	; space between two identifiers
     (pbreak 0 0)
     (print-tm y 'listcomb pcrator)
  )))			; print-listcomb


; print a user-defined infix operator
(de print-infixcomb (tml pcrator)
    (print-tm (second tml) 'infixcomb pcrator)
    (ptoken | |)
    (pstring (get-const-name (first tml)))
    (pbreak 1 0)
    (print-tm (third tml) 'infixcomb pcrator)) 	; print-infixcomb




; print a formula
(de print-fm (fm op1)
  (let ((op2 (form-class fm)))
   (let ((cl (closes op1 op2)))
     (if cl (ptoken |(|))
     (pbegin 0)
     (selectq op2
       ((conj disj imp iff) (print-conn-form fm))
       (neg (print-neg-form fm))
       (pred (print-pred-form fm))
       (infixpred (print-infix-pred fm))
      ((forall exists) (print-quant-form fm))
      (t (lcferror 'print-fm)))
     (pend)
     (if cl (ptoken |)|))
   )))  ;print-fm


; print a formula built from a connective
; suppress parentheses using right-associativity
(de print-conn-form (fm)
  (let ((conn (get-conn fm)))
   (while (eq conn (get-conn fm))
      (print-fm (get-left-form fm) conn)
      (selectq (get-conn fm)
	  (conj (ptoken |  /\\|))
	  (disj (ptoken |  \\/|))
	  (imp  (ptoken |  ==>|))
	  (iff  (ptoken |  <=>|)))
      (pbreak 2 0)
      (setq fm (get-right-form fm)))
    (print-fm fm conn)))  ; print-conn-form


; print negation
(de print-neg-form (fm)
    (ptoken |~ |)
    (print-fm (second fm) 'neg))  	; print-neg-form



; print an infix predicate
(de print-infix-pred (fm)
      (let (((sym arg1 arg2) (cdr fm)))
	(print-tm arg1 nil nil)
	(selectq sym
	  (|equiv| (ptoken | ==|))
	  (|inequiv| (ptoken | <<|))
	  (t (ptoken | |) (pstring sym)))
	(pbreak 1 0)
	(print-tm arg2 nil t)))			; print-infix-pred

; print a predicate formula
(de print-pred-form (fm)
    (pstring (get-pred-sym fm))
    (pbreak 1 0)
    (print-tm (get-pred-arg fm) t t))	; print-pred-form


; print !x y z.w  instead of !x. !y. !z. w
; this makes a big difference if the formula is broken over several lines
(de print-quant-form (fm)
  (let ((quant (get-quant fm)))
    (pbegin 1)
    (if (eq quant 'forall) (ptoken |!|) (ptoken |?|))
    (print-tm (get-quant-var fm) quant t)
    (let ((body (get-quant-body fm)))
      (while (eq (form-class body) quant)
	     (pbreak 1 0)
	     (print-tm (get-quant-var body) quant t)
	     (setq body (get-quant-body body)))
      (ptoken |.|)
      (pend)
      (pbreak 1 1)
      (print-fm body quant))))  ;prquant


; print a type
(de print-ty (ty op1)
 (let ((op2 (type-class ty)))
   (selectq op2
    (%VARTYPE (pstring(get-vartype-name ty)))
    ((|prod| |sum| |fun|)
       (let ((cl (closes op1 op2)) (tyargs (get-type-args ty)))
	(if cl (ptoken |(|))
	(pbegin 0)
	(print-ty (first tyargs) op2)
	(selectq op2
	    (|prod| (ptoken | *|))
	    (|sum| (ptoken | +|))
	    (|fun| (ptoken | ->|))
	    (t (lcferror "bad type - print-ty")))
	(pbreak 1 0)
	(print-ty (second tyargs) op2)
	(pend)
	(if cl (ptoken |)|))))
    (t (print-named-type ty)))))  ;print-ty



; Print named type, with its type arguments
(de print-named-type (ty)
  (let ((tyname (get-type-op ty))  (tyargs (get-type-args ty)))
   (cond ((null tyargs) (pstring tyname))
      (t (pbegin 0)
	 (pbegin 1)
	 (ptoken |(|)
	 (print-ty (first tyargs) nil)  ;nil added V3.2
	 (mapc '(lambda (ty) (ptoken |,|) (pbreak 0 0) (print-ty ty nil))
	       (cdr tyargs))
	 (pend)
	 (ptoken |)|)
	 (pbreak 0 0)
	 (pstring tyname)
	 (pend)))))  ;print-named-type

