;***************************************************************************
;*
;*	L-inst
;*
;**************************************************************************
;* Original: F-inst (Cambridge LCF)
;* Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)
;*
;* object language type instantiation
;* Sharing relationships in types must be detected -- dumb algorithms that
;* expand type DAGs into trees will consume exponential time and space!
;* This particularly holds for algorithms that traverse all types of a term,
;* for note the duplication of types in combinations:
;*		((F : ty1 -> ty2)  (X : ty1))  : ty2
;* The instantiation of terms and formulas is now implemented in Lisp,
;* as the ML versions were exponential.

(eval-when (compile)
         (include S-constants)
	 (include llmac)
	 (include S-macro)
	 (include L-ol-rec)
	 (genprefix inst))


; *********************************************
; this function is necessary for search in %insttyl since it is now
; represented as list of lisp lists and not lisp pairs!
(de revasslist (tt l)
   (cond
	((null l) nil)
	((equal (cadar l) tt);
	   (caar l))
	(t (revasslist tt (cdr l)))
   );end cond
);end revasslist


(dml |paired_type_in_type| 2 ml-type_in_type 
  (mk-funtyp (mk-tupletyp (type) (type)) (bool)))
(dml |paired_type_in_term| 2 ml-type_in_term 
  (mk-funtyp (mk-tupletyp (type) (term)) (bool)))
(dml |paired_type_in_form| 2 ml-type_in_form 
  (mk-funtyp (mk-tupletyp (type) (form)) (bool)))


(defun ml-type_in_type (%ty ty)
   (let ((%oldtys nil)) (type-in-type ty)))


; does %ty occur anywhere inside ty?
; record compound types already seen to avoid re-traversal
(defun type-in-type (ty)
 (cond ((memq ty %oldtys) nil)
       ((equal ty %ty) t)
       ((not (is-vartype ty))
	  (prog1 (exists 'type-in-type (cdr (ml-dest_type ty)))
		 (newl %oldtys ty)))
     ))  ;type-in-type



(defun ml-type_in_form (%ty ob)
   (let ((%oldtys nil)) (type-in-fm ob)))


(defun ml-type_in_term (%ty ob)
   (let ((%oldtys nil)) (type-in-tm ob)))


; does %ty appear in the formula?
(defun type-in-fm (fm)
  (selectq (form-class fm)
    ((conj disj imp iff)
     (or (type-in-fm (get-left-form fm)) (type-in-fm (get-right-form fm))))
    ((forall exists)
     (or (type-in-tm (get-quant-var fm)) (type-in-fm (get-quant-body fm))))
    (pred (type-in-tm (get-pred-arg fm)))
    (t (lcferror (cons fm '|type-in-fm|))))
 )    ; type-in-fm


; does %ty appear in the term?
(defun type-in-tm (tm)
  (selectq (term-class tm)
    ((var const) (type-in-type (get-type tm)))
    (abs (or (type-in-tm (get-abs-var tm)) (type-in-tm (get-abs-body tm))))
    (comb (or (type-in-tm (get-rator tm)) (type-in-tm (get-rand tm))))
    (t (lcferror '|type-in-tm|)))
 )    ; type-in-tm


; *********************************************

(dml |type_tyvars| 1 ml-type-tyvars 
  (mk-funtyp (type) (list (type))))
(dml |term_tyvars| 1 ml-term_tyvars 
   (mk-funtyp (term) (list (type))))
(dml |form_tyvars| 1 ml-form_tyvars 
   (mk-funtyp (form) (list (type))))


(defun ml-type-tyvars  (ty)
  (let ((%tyvl nil) (%oldtys nil))
    (tyvars-type ty)
    (nreverse %tyvl)))		; ml-type-tyvars


; find all type variables in a type
(defun tyvars-type (ty)
 (cond ((memq ty %oldtys))
       ((is-vartype ty) (setq %tyvl (inq ty %tyvl)))
       (t (mapc 'tyvars-type (cdr (ml-dest_type ty)))
	  (newl %oldtys ty))	
 ))   ; tyvars



(defun ml-form_tyvars(ob)
  (let ((%tyvl nil) (%oldtys nil))
    (tyvars-fm ob)
    (nreverse %tyvl)))


(defun ml-term_tyvars(ob)
  (let ((%tyvl nil) (%oldtys nil))
    (tyvars-tm ob)
    (nreverse %tyvl)))


; find all type variables in a formula
(defun tyvars-fm (fm)
  (selectq (form-class fm)
    ((conj disj imp iff)
     (tyvars-fm (get-left-form fm)) (tyvars-fm (get-right-form fm)))
    ((forall exists)
     (tyvars-tm (get-quant-var fm)) (tyvars-fm (get-quant-body fm)))
    (pred (tyvars-tm (get-pred-arg fm)))
    (t (lcferror (cons fm '|tyvars-fm|))))
  )						; tyvars-fm


; find all type variables in a term
(defun tyvars-tm (tm)
  (selectq (term-class tm)
    ((var const) (tyvars-type (get-type tm)))
    (abs (tyvars-tm (get-abs-var tm)) (tyvars-tm (get-abs-body tm)))
    (comb (tyvars-tm (get-rator tm)) (tyvars-tm (get-rand tm)))
    (t (lcferror '|tyvars-tm|)))
 )    ; tyvars-tm


; *********************************************

; type instantiation

; Renames variables to ensure that no distinct variables become identical
; after instantiation -- makes variants of all (and ONLY) those
; variables whose types change and whose names match.
; The first argument of inst_term and inst_form is
; a list of variables whose names must not be used.
; This handles free variables in the assumption list for the rule INSTTYPE.



(dml |paired_inst_type| 2 ml-inst_type
   (mk-funtyp (mk-tupletyp
	(list (mk-tupletyp (type) (type))) (type)) (type)))
(dml |paired_inst_term| 3 ml-inst_term
   (mk-funtyp
	(mk-tupletyp (list (term)) (list (mk-tupletyp (type) (type))) (term))
	(term)
   );end
);end
(dml |paired_inst_form| 3 ml-inst_form
  (mk-funtyp
	(mk-tupletyp (list (term)) (list (mk-tupletyp (type) (type)) )(form))
	(form)
   );end mk-fun
);end


(defun ml-inst_type (%insttyl ty)
   (if %insttyl (instin-type ty) ty))  ;ml-instintype


(defun ml-inst_form (used-vars %insttyl ob)
   (if %insttyl
       (let ((%renames nil)
	   (%changed-types (mapcar 'cadr %insttyl))
	   (%used-varnames (var-name-list used-vars 'inst))) 
	  (instin-fm ob))
       ob))			; ml-inst-in-fm

; GH:duplicated code of ml-inst-in for forms and terms
(defun ml-inst_term (used-vars %insttyl ob)
   (if %insttyl
       (let ((%renames nil)
	   (%changed-types (mapcar 'cadr %insttyl))
	   (%used-varnames (var-name-list used-vars 'inst))) 
	  (instin-tm ob))
       ob))			; ml-inst-in-tm


; instantiate types in a type
; record values of compound types to save re-traversal
(defun instin-type (ty)
 (cond
  ((revasslist ty %insttyl))
  ((is-vartype ty) ty)
  ((let (( (tyop . tyargs) (ml-dest_type ty)))
     (let ((newty (make-type tyop (mapcar 'instin-type tyargs))))
	(newl %insttyl (list newty ty));changed cons -> list
	newty))
 )))  ;instin-type

; instantiate types in a formula
(defun instin-fm (fm)
  (selectq (form-class fm)
     ((conj disj imp iff)
      (make-conn-form (get-conn fm)
	  (instin-fm (get-left-form fm))
	  (instin-fm (get-right-form fm))))
     ((forall exists)
      (make-quant-form (get-quant fm)
	  (instin-tm (get-quant-var fm))
	  (instin-fm (get-quant-body fm))))
     (pred (make-pred-form (get-pred-sym fm)
	       (instin-tm (get-pred-arg fm))))
     (t (lcferror 'instin-fm)))
)    ; instin-fm



; instantiate types in a term
(defun instin-tm (tm)
  (selectq (term-class tm)
    (var (instin-var tm))
    (const (ml-mk_const (get-const-name tm)
	       (instin-type (get-type tm))))
    (abs (ml-mk_abs (instin-tm (get-abs-var tm))
	      (instin-tm (get-abs-body tm))))
    (comb (let ((rator (instin-tm (get-rator tm)))
		(rand  (instin-tm (get-rand tm))))
	     (let ((tyargs (cdr (ml-dest_type (get-type rator)))))
		(make-comb rator rand (second tyargs)))))
    (t (lcferror 'instin-tm)))
)    ; instin-tm
	

; instantiate types in a variable
; renames variables whose type may change
; the new name differs from all previous names
(defun instin-var (tm)
 (let ((name (get-var-name tm)) (ty (get-type tm)))
  (cond ((assq1 tm %renames))
	((exists '(lambda (cty) (ml-type_in_type cty ty))
		 %changed-types)
	  (let ((newname (variant-name %used-varnames name)))
	     (let ((newv (mk_realvar newname (instin-type ty))))
		(newl %used-varnames newname)
		(newl %renames (cons tm newv))
		newv)))
	(t (newl %renames (cons tm tm)) tm))
 ))   ; instin-var



; variable renaming - primarily for storing axioms and theorems
; forces all variable names in a scope to be distinct
; creates new names (identifiers) for all genvars

; We don't allow genvars on theory files because
; calling genvar should always make a variable not already present
; in the current LCF session (in particular, not read from a theory file).

; the implementation of scopes should be changed to use an environment,
; without side-effects, rather than the hack of forget-var

(dml |rename_term| 1 ml-rename_term (mk-funtyp (term) (term)))
(dml |rename_form| 1 ml-rename_form (mk-funtyp (form) (form)))


(defun ml-rename_form (ob)
  (let ((%renames nil)  (%used-varnames nil))
       (rename-vars-fm ob)))


(defun ml-rename_term (ob)
  (let ((%renames nil)  (%used-varnames nil))
       (rename-vars-tm ob)))


; rename variables in a formula
(defun rename-vars-fm (fm)
  (selectq (form-class fm)
     ((conj disj imp iff)
      (make-conn-form (get-conn fm)
	  (rename-vars-fm (get-left-form fm))
	  (rename-vars-fm (get-right-form fm))))
     ((forall exists)
      (let ((quant (get-quant fm))
	    (bv (rename-vars-tm (get-quant-var fm)))
	    (body (rename-vars-fm (get-quant-body fm))))
	   (forget-var (get-quant-var fm))
	   (make-quant-form quant bv body)))
     (pred (make-pred-form (get-pred-sym fm)
	       (rename-vars-tm (get-pred-arg fm))))
     (t (lcferror 'rename-vars-fm )))
)    ; rename-vars-fm



; rename variables in a term
(defun rename-vars-tm (tm)
  (selectq (term-class tm)
    (var (rename-var tm))
    (const tm)
    (abs (let ((bv (rename-vars-tm (get-abs-var tm)))
	       (body (rename-vars-tm (get-abs-body tm))))
	      (forget-var (get-abs-var tm))
	      (ml-mk_abs bv body)))
    (comb (ml-mk_comb (rename-vars-tm (get-rator tm))
	     (rename-vars-tm (get-rand tm))))
    (t (lcferror 'rename-vars-tm)))
)    ; rename-vars-tm
	

; rename a variable
; primes each variable to differ from all previous names
; renames all genvars
(defun rename-var (v)
 (let ((name (get-var-name v)) (ty (get-type v)))
  (cond ((assq1 v %renames))
	(t (let ((newname (variant-name %used-varnames 
			      (if (idenp name) name (intern (gensym))))))
	     (let ((newv (mk_realvar newname ty)))
		(newl %used-varnames newname)
		(newl %renames (cons v newv))
		newv))))
 ))   ; rename-var


; forget about a variable once leaving its scope
; to allow (\x.x), (\x.x) without priming the second x 
; change needed by Mike Gordon
(defun forget-var (v)
  (let ((v2 (assq1 v %renames)))
     (setq %used-varnames (delq (get-var-name v2) %used-varnames))
     (newl %renames (cons v nil)))
)				; forget-var
