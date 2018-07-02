;*****************************************************************************
;*
;*	OL-SYNTAX
;*
;******************************************************************************
; Object Language Abstract Syntax
; Original : F-ol-syntax (Cambridge LCF)
; Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)


(eval-when (compile)
  (include S-constants)
  (include llmac)
  (include S-macro)
  (include L-ol-rec)
  (genprefix ol-syntax))

; for writing destructor functions
(defmacro destruct (tag x msg)
   `(cond ((eq (car ,x) (quote ,tag)) (cdr ,x))
	  (t (msg-failwith '|syntax| ,msg)))
       )  ;destruct

; antiquotation

(de q-mk_antiquot (ob) (cons '%ANTIQUOT ob))	; q-mk_antiquot

; predicates

(de q-mk_pred (tok tm)
    (if (unify (omutant (predicatep tok)) (q-typeof tm))
	(make-pred-form tok tm)
	(msg-failwith '|syntax| '|mk_pred|)))   ; q-mk_pred

(dml |mk_pred| 2 q-mk_pred (mk-funtyp (mk-tupletyp (string) (term)) (form)))

(de ml-is_pred (fm) (eq (form-class fm) 'pred))  ;ml-is_pred
(dml |is_pred| 1 ml-is_pred (mk-funtyp (form) (bool)))

(de ml-dest_pred (fm) (destruct pred fm '|dest_pred|))  ;ml-dest_pred
(de ml-dest_pred1 (fm) (dupl_tupl (ml-dest_pred fm)))
(dml |dest_pred| 1 ml-dest_pred1 (mk-funtyp (form) (mk-tupletyp (string) (term))))

; conjunction

(de q-mk_conj (fm1 fm2) (make-conn-form 'conj fm1 fm2))  ;q-mk_conj

(dml |mk_conj| 2 q-mk_conj (mk-funtyp (mk-tupletyp (form) (form)) (form)))

(de ml-is_conj (fm) (eq (form-class fm) 'conj))  ;ml-is_conj
(dml |is_conj| 1 ml-is_conj (mk-funtyp (form) (bool)))

(de ml-dest_conj (fm) (destruct conj fm '|dest_conj|))  ;ml-dest_conj
(de ml-dest_conj1 (fm) (dupl_tupl (ml-dest_conj fm)))
(dml |dest_conj| 1 ml-dest_conj1 (mk-funtyp (form) (mk-tupletyp (form) (form))))


; disjunction

(de q-mk_disj (fm1 fm2) (make-conn-form 'disj fm1 fm2))  ;q-mk_disj
(dml |mk_disj| 2 q-mk_disj (mk-funtyp (mk-tupletyp (form) (form)) (form)))

(de ml-is_disj (fm) (eq (form-class fm) 'disj))  ;ml-is_disj
(dml |is_disj| 1 ml-is_disj (mk-funtyp (form) (bool)))

(de ml-dest_disj (fm) (destruct disj fm '|dest_disj|))  ;ml-dest_disj
(de ml-dest_disj1 (fm) (dupl_tupl (ml-dest_disj fm)))
(dml |dest_disj| 1 ml-dest_disj1 (mk-funtyp (form) (mk-tupletyp (form) (form))))



; implication

(de q-mk_imp (fm1 fm2) (make-conn-form 'imp fm1 fm2))  ;q-mk_imp
(dml |mk_imp| 2 q-mk_imp (mk-funtyp (mk-tupletyp (form) (form)) (form)))

(de ml-is_imp (fm)  (eq (form-class fm) 'imp))  ;ml-is_imp
(dml |is_imp| 1 ml-is_imp (mk-funtyp (form) (bool)))

(de ml-dest_imp (fm) (destruct imp fm '|dest_imp|))  ;ml-dest_imp
(de ml-dest_imp1 (fm) (dupl_tupl (ml-dest_imp fm)))
(dml |dest_imp| 1 ml-dest_imp1 (mk-funtyp (form) (mk-tupletyp (form) (form))))



; if-and-only-if

(de q-mk_iff (fm1 fm2) (make-conn-form 'iff fm1 fm2))  ;q-mk_iff
(dml |mk_iff| 2 q-mk_iff (mk-funtyp (mk-tupletyp (form) (form)) (form)))

(de ml-is_iff (fm) (eq (form-class fm) 'iff))  ;ml-is_iff
(dml |is_iff| 1 ml-is_iff (mk-funtyp (form) (bool)))

(de ml-dest_iff (fm)  (destruct iff fm '|dest_iff|))  ;ml-dest_iff
(de ml-dest_iff1 (fm) (dupl_tupl (ml-dest_iff fm)))
(dml |dest_iff| 1 ml-dest_iff1 (mk-funtyp (form) (mk-tupletyp (form) (form))))

; negation is a special case of implication, thus no destructors, etc.

(de q-mk_neg (fm) (make-conn-form 'imp fm %falsity))  ;q-mk_neg

; universal quantifier

(de q-mk_forall (v fm)
 (let ((v (strip-antiquot v)))
   (q-free-var v)
   (ml-mk_forall v fm))
 )  ;q-mk_forall

(de ml-mk_forall (v fm)
 (if (is-var v) (make-quant-form 'forall v fm)
     (msg-failwith '|syntax| '|mk_forall|)))  ;ml-mk_forall

(dml |mk_forall| 2 ml-mk_forall (mk-funtyp (mk-tupletyp (term) (form)) (form)))

(de ml-is_forall (fm)  (eq (form-class fm) 'forall))  ;ml-is_forall
(dml |is_forall| 1 ml-is_forall (mk-funtyp (form) (bool)))

(de ml-dest_forall (fm)  (destruct forall fm '|dest_forall|)) ;ml-dest_forall
(de ml-dest_forall1 (fm) (dupl_tupl (ml-dest_forall fm)))
(dml |dest_forall| 1 ml-dest_forall1 (mk-funtyp (form) (mk-tupletyp (term) (form))))



; existential quantifier


(de q-mk_exists (v fm)
 (let ((v (strip-antiquot v)))
  (q-free-var v)
  (ml-mk_exists v fm))
 )  ;q-mk_exists

(de ml-mk_exists (v fm)
 (if (is-var v) (make-quant-form 'exists v fm)
     (msg-failwith '|syntax| '|mk_exists|)))  ;ml-mk_exists

(dml |mk_exists| 2 ml-mk_exists (mk-funtyp (mk-tupletyp (term) (form)) (form)))

(de ml-is_exists (fm)  (eq (form-class fm) 'exists))  ;ml-is_exists
(dml |is_exists| 1 ml-is_exists (mk-funtyp (form) (bool)))

(de ml-dest_exists (fm)  (destruct exists fm '|dest_exists|))  ;ml-dest_exists
(de ml-dest_exists1 (fm) (dupl_tupl (ml-dest_exists fm)))
(dml |dest_exists| 1 ml-dest_exists1 (mk-funtyp (form) (mk-tupletyp (term) (form))))


; equivalence and inequivalence are special cases of predicates
; thus no destructors, etc.

(de q-mk_equiv (tm1 tm2)
  (let ((tm (catch (q-mk_pred '|equiv| (q-mk_pair tm1 tm2)) evaluation)))
     (cond ((eq (car tm) 'pac) (msg-failwith '|syntax| '|mk_equiv|))
	   (t tm))))   ; q-mk_equiv

(de q-mk_inequiv (tm1 tm2)
  (let ((tm (catch (q-mk_pred '|inequiv| (q-mk_pair tm1 tm2)) evaluation)))
     (cond ((eq (car tm) 'pac) (msg-failwith '|syntax| '|mk_inequiv|))
	   (t tm))))   ; q-mk_inequiv

; variables

; In a quotation, all variables with the same name are identical --
; the alist %vtyl makes sure of that.
(de q-mk_var (tok)
  (make-var tok
    (or (assoc1 tok %vtyl)
	(new-var-type tok)))
  )  ;q-mk_var


; create a new type variable and put it on %vtyl
(de new-var-type (tok)
  (let ((newty (genlink)))
       (newl %vtyl (cons tok newty))
       newty))			; new-var-type


; allows bound variables of the same name to be independent
(de q-free-var (v)
  (if (is-var v) (new-var-type (get-var-name v)))
)				; q-free-var



; variable names must be identifiers
; thus genvars will be distinct from any other variables
(de ml-mk_var (tok ty)
 (if (or (constp tok) (not (idenp tok))) (msg-failwith '|syntax| '|mk_var|)
     (mk_realvar tok ty)))  ;ml-mk_var

; set up sharing so equivalent variables are "eq"
(de mk_realvar (tok ty)
   (or (assoc1 ty (get tok '|mk_var|))
       (cdr (consprop tok (cons ty (make-var tok ty)) '|mk_var|))))
				; mk_realvar

(dml |mk_var| 2 ml-mk_var (mk-funtyp (mk-tupletyp (string) (type)) (term)))

; Generate a variable, with name that can't conflict with any other
; (presuming that genvars cannot be read from theory files)
;  the name is interned to avoid weird consequences
(de ml-genvar  (ty) (mk_realvar (intern (uniquesym 'gen 'var)) ty))  ;ml-genvar

(de ml-is_var (term)  (eq (term-class term) 'var))  ;ml-is_var
(dml |is_var| 1 ml-is_var (mk-funtyp (term) (bool)))

(de ml-dest_var (tm) (destruct var tm 'dest_var))  ;ml-dest_var
(de ml-dest_var1 (tm)  (dupl_tupl (ml-dest_var tm)))
(dml |dest_var| 1 ml-dest_var1 (mk-funtyp (term) (mk-tupletyp (string) (type))))



; constants

(de q-mk_const (tok) (make-const tok (omutant (constp tok))))  ;q-mk_const

; includes code to share constants of identical types
; (this wastes storage...does it do any good?)
(de ml-mk_const (tok ty)
   (cond
    ((assoc1 ty (get tok '|mk_const|)))
    ((and (constp tok) (unify ty (omutant(constp tok))))
     (cdr (consprop tok (cons ty (make-const tok ty)) '|mk_const|)))
    (t (msg-failwith '|syntax| '|mk_const|)))
  )  ;ml-mk_const

(dml |mk_const| 2 ml-mk_const (mk-funtyp (mk-tupletyp (string) (type)) (term)))

(de ml-is_const (term)  (eq (term-class term) 'const))  ;ml-is_const
(dml |is_const| 1 ml-is_const (mk-funtyp (term) (bool)))

(de ml-dest_const (tm) (destruct const tm 'dest_const))  ;ml-dest_const
(de ml-dest_const1 (tm) (dupl_tupl (ml-dest_const tm)))
(dml |dest_const| 1 ml-dest_const1 (mk-funtyp (term) (mk-tupletyp (string) (type))))



; abstractions

(de q-mk_abs (v tm)
    (let ((v (strip-antiquot v)))
      (q-free-var v)
      (ml-mk_abs v tm))
 )  ;q-mk_abs

(dml |mk_abs| 2 ml-mk_abs (mk-funtyp (mk-tupletyp (term) (term)) (term)))

(de ml-mk_abs (v tm)
    (if (is-var v)
        (make-abs v tm (make-type '|fun| (list (q-typeof v) (q-typeof tm))))
	(msg-failwith '|syntax| '|mk_abs|)))  ;ml-mk_abs

(dml |is_abs| 1 ml-is_abs (mk-funtyp (term) (bool)))
(de ml-is_abs (term)  (eq (term-class term) 'abs))  ;ml-is_abs

; different from other destructors -- throws away the type
(de ml-dest_abs (tm) (car (destruct abs tm 'dest_abs)))  ;ml-dest_abs
(de ml-dest_abs1 (tm) (dupl_tupl (ml-dest_abs tm)))
(dml |dest_abs| 1 ml-dest_abs1 (mk-funtyp (term) (mk-tupletyp (term) (term))))



; combinations

(de q-mk_comb (tm1 tm2)
  (let ((ty (genlink)))
       (if (unify (q-typeof tm1) (make-type '|fun| (list (q-typeof tm2) ty)))
	   (make-comb tm1 tm2 ty)
	   (msg-failwith '|syntax| '|mk_comb|))))  ;q-mk_comb


; q-mk_comb tries to unify types while ml-mk_comb expects an exact match
;    and returns a type free of links.
(de ml-mk_comb (tm1 tm2)
  (let (((tyop . tyargs)
	   (failtrap '(lambda (tok) (msg-failwith '|syntax| '|mk_comb|))
	       (ml-dest_type (get-type tm1)))))
     (if (and (eq tyop '|fun|) (equal (first tyargs)(get-type tm2)))
	   (make-comb tm1 tm2 (second tyargs))
	   (msg-failwith '|syntax| '|mk_comb|)))
	  )  ;ml-mk_comb

(dml |mk_comb| 2 ml-mk_comb (mk-funtyp (mk-tupletyp (term) (term)) (term)))

(de ml-is_comb (term)  (eq (term-class term) 'comb))  ;ml-is_comb
(dml |is_comb| 1 ml-is_comb (mk-funtyp (term) (bool)))

(de ml-dest_comb (tm) (car (destruct comb tm '|dest_comb|)))  ;ml-dest_comb
(de ml-dest_comb1 (tm) (dupl_tupl (ml-dest_comb tm)))
(dml |dest_comb| 1 ml-dest_comb1 (mk-funtyp (term) (mk-tupletyp (term) (term))))



; other terms

; put a type constraint onto a term
; the type is antiquoted for efficiency
;    to prevent canon-ty from traversing it
(de q-mk_typed (tm ty)
  (if (unify (q-typeof tm) (q-mk_antiquot ty)) tm
      (msg-failwith '|syntax| '|mk_typed|))
 )  ;q-mk_typed


(de q-mk_pair (tm1 tm2) (q-mk_comb (q-mk_comb (q-mk_const 'PAIR) tm1) tm2))  ;q-mk_pair

(de q-mk_cond (tm1 tm2 tm3)
    (q-mk_comb (q-mk_comb (q-mk_comb (q-mk_const 'COND) tm1) tm2) tm3)
)  ;q-mk_cond




; vartypes

; create a vartype, maintaining sharing so equivalent vartypes are "eq"
(de q-mk_vartype (tok)
  (cond
    ((get tok '|mk_vartype|))
; typevariables now as in SML (2/2/87)
;    ((eq (first (exploden tok)) #/*) 
     ((is_type_var tok)
	(putprop tok (make-vartype tok) '|mk_vartype|))
    ((msg-failwith '|syntax| '|mk_vartype|))
    ))  ;q-mk_vartype

(dml |mk_vartype| 1 q-mk_vartype (mk-funtyp (string) (type)))

(de ml-is_vartype (ty)  (eq (type-class ty) '%VARTYPE))  ;ml-is_vartype
(dml |is_vartype| 1 ml-is_vartype (mk-funtyp (type) (bool)))

(de ml-dest_vartype (ty)
 (if (is-vartype ty) (get-vartype-name ty)
     (msg-failwith '|syntax| '|dest_vartype|)))  ;ml-dest_vartype

(dml |dest_vartype| 1 ml-dest_vartype (mk-funtyp (type) (string)))



; compound types

; make a compound type ... check number of arguments
(de q-mk_type (op tylist)
  (cond ((not (eq (get op 'olarity) (length tylist)))
	  (msg-failwith '|syntax| '|mk_type|))
        ((null tylist) (get op 'canon))
        (t (make-type op tylist))))
  ;q-mk_type

(dml |mk_type| 2 q-mk_type  (mk-funtyp (mk-tupletyp (string) (list (type)))
				       (type)))


; no discriminator -- use (not is_vartype)


(de ml-dest_type (ty)
   (if (is-vartype ty) (msg-failwith '|syntax| '|dest_type|) ty))  ;ml-dest_type
(de ml-dest_type1 (ty) (dupl_tupl (ml-dest_type ty)))
(dml |dest_type| 1 ml-dest_type1 (mk-funtyp (type)
				   (mk-tupletyp (string) (list (type)))))

; type of any term

(de ml-type_of (tm)  (get-type tm))  ;ml-type_of
(dml |type_of| 1 ml-type_of (mk-funtyp (term) (type)))


; type of a term in a quotation
(de q-typeof (tm) (get-type (strip-antiquot tm)))  ;q-typeof


; Skip over ANTIQUOT nodes
(de strip-antiquot (ob) (while (is-antiquot ob) (setq ob (cdr ob))) ob)  ; strip-antiquot


(setq %thm-count 0)		; count theorems inferred in session


(de ml-thm_count (x) %thm-count) ;ml-thm_count
(dml |thm_count| 1 ml-thm_count (mk-funtyp (unit) (int)))

;need not be interfaced by dupl_tupl (sq is already a tuple)
(de ml-mk_thm (sq)  (incr %thm-count)  sq)  ;ml-mk_thm
(dml |mk_thm| 1 ml-mk_thm (mk-funtyp (mk-tupletyp (list (form)) (form))
				   (thm)))

;sme for this function
(de ml-dest_thm (sq)  sq)  ;ml-dest_thm
(dml |dest_thm| 1 ml-dest_thm (mk-funtyp (thm) (mk-tupletyp (list (form)) (form))))


; the following function definitions depend on the Lisp representation
; of theorems, terms, and formulas.
;does not make a difference to interface this one (car dupl) = (car tupl)!
(dml |hyp| 1 car (mk-funtyp (thm) (list (form))))

;changed this one from cdr to cadr !
(dml |concl| 1 cadr (mk-funtyp (thm) (form)))

; if tok is a predicate symbol, then return its type, else nil
(de predicatep (tok) (get tok 'predicate))  ; predicatep

; if tok is a constant symbol, then return its type, else nil
(de constp (tok) (get tok 'const))  ;constp

; the predicate FALSITY()
(setq %empty (make-const '|()| (make-type '|void| nil)))
(setq %falsity (make-pred-form 'FALSITY %empty))


(dml |term_class| 1 car (mk-funtyp (term) (string)))
(dml |form_class| 1 car (mk-funtyp (form) (string)))


(dml |genvar| 1 ml-genvar (mk-funtyp (type) (term)))
