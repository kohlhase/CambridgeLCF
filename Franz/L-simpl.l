;**************************************************************************
;*
;*	L-simpl
;:
;**************************************************************************
;* Original: F-simpl (Cambridge LCF)
; Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)


(eval-when (compile)
  (include S-constants)
  (include llmac)
  (include S-macro)
  (include L-ol-rec)
  (genprefix simpl))

; unlike the F-simpl written by Chris Wadsworth, these matching functions
; do not preprocess the patterns for faster matching.  They are simpler
; to use, their implementation is much cleaner, and they are almost as
; efficient as their predecessors.  For fast matching, the OL network
; functions can be used.

; term_match and form_match now match types as well as terms.

; match a pattern pat to an object ob
;   returns nil to indicate failure
;   records match in specials %substl and %insttyl


(defun form-match (pat ob)
  (and (eq (form-class pat) (form-class ob))
       (selectq (form-class pat)
	 ((conj disj imp iff)
	  (and (form-match (get-left-form pat) (get-left-form ob))
	       (form-match (get-right-form pat) (get-right-form ob))))
	 ((forall exists)
	  (let ((pbv (get-quant-var pat))  (obv (get-quant-var ob)))
	    (and (type-match (get-type pbv) (get-type obv))
		 (let ((%bv-pairs (cons (cons pbv obv) %bv-pairs)))
		   (form-match (get-quant-body pat) (get-quant-body ob))))))
	 (pred (and (eq (get-pred-sym pat) (get-pred-sym ob))
		    (term-match (get-pred-arg pat) (get-pred-arg ob))))
	 (t (lcferror 'form-match)))))		; form-match


(defun term-match (pat ob)
  (selectq (term-class pat)
    (const (and (is-const ob)
		(eq (get-const-name pat) (get-const-name ob))
		(type-match (get-type pat) (get-type ob))))
    (var  (var-match pat ob))
    (comb (and (is-comb ob)
	       (term-match (get-rator pat) (get-rator ob))
	       (term-match (get-rand pat) (get-rand ob))))
    (abs (and (is-abs ob)
	      (let ((pbv (get-abs-var pat)) (obv (get-abs-var ob)))
		(type-match (get-type pbv) (get-type obv))
		(let ((%bv-pairs (cons (cons pbv obv) %bv-pairs)))
		  (term-match (get-abs-body pat) (get-abs-body ob))))))
    (t (lcferror 'term-match))))		;term-match

; match a variable to an object
(defun var-match (var ob)
  (let ((pbind (assq var %bv-pairs)) (obind (revassq ob %bv-pairs)))
    (cond ((or pbind obind) (eq pbind obind))	; corresponding bound vars
	  ((not (exists '(lambda (vv) (freein-tm (cdr vv) ob)) %bv-pairs))
						; ob is free in entire object
	   (let ((prev (revassq1 var %substl)))	; keep consistent
	     (cond (prev (alphaconv ob prev))	; with prev match
		   ((type-match (get-type var) (get-type ob))
		    (newl %substl (cons  ob var)))))))))	; var-match

; match a pattern type with an object type, return nil if failure
; records types that are known to match, to prevent exponential blow-up
(defun type-match (pty ty)
  (if (is-vartype pty)
      (let ((ty2 (revasslist pty %insttyl)))
	(if ty2 (equal ty ty2)			; consistent with previous match
	    (newl %insttyl (list ty pty))))
      (let ((pty-tys (assq pty %type-matches)))
	(or (memq ty (cdr pty-tys))
	    (cond ((is-vartype ty) (msg-failwith '|general| '|type_match|))
		  ((and (eq (get-type-op pty) (get-type-op ty))
			(forall 'type-match
				(get-type-args pty) 
				(get-type-args ty)))
						; record matching pair of types
		   (if pty-tys
		       (rplacd pty-tys (cons ty (cdr pty-tys)))
		       (newl %type-matches (cons pty (list ty))))
		   t))))))			;type-match

; instantiate types in variables
; and strip out null matches of the form (v . v)
; to minimize the variables that must be instantiated
; (null matches must first be recorded
;    to prevent v from matching something else)
(defun prepare-substl (substl)
    (if substl
	(let (( ((tm . var) . tail) substl))
	  (let ((var2 (mk_realvar (get-var-name var) (get-type tm))))
	    (if (eq tm var2) (prepare-substl tail)
		(cons (list tm var2) (prepare-substl tail))))))) ; prepare-substl

; prepare the type instantiation list
; by stripping out redundant lists (*  *)
(defun prepare-insttyl (insttyl)
  (if insttyl
      (let ((head (car insttyl)) (tail (cdr insttyl)))
	(if (eq (car head) (cadr head)) (prepare-insttyl tail)
	    (cons head (prepare-insttyl tail))))))	; prepare-insttyl


(defun ml-term_match (pat ob)
  (let ((%substl nil) (%insttyl nil) (%bv-pairs nil) (%type-matches nil))
    (ifn (term-match pat ob) (msg-failwith '|general| '|term_match|))
    (cons (prepare-substl %substl) (prepare-insttyl %insttyl))))	; ml-form_match

(defun ml-form_match (pat ob)
  (let ((%substl nil) (%insttyl nil) (%bv-pairs nil) (%type-matches nil))
    (ifn (form-match pat ob) (msg-failwith '|general| '|form_match|))
    (cons (prepare-substl %substl) (prepare-insttyl %insttyl))))	; ml-form_match

(de ml-term_match1 (pat ob)
   (let ((a (ml-term_match pat ob)))
	(list (car a) (cdr a))
   )
);end

(de ml-form_match1 (pat ob)
   (let ((a (ml-form_match pat ob)))
	(list (car a) (cdr a))
   )
);end

(dml |paired_term_match| 2 ml-term_match1
 (mk-funtyp
  (mk-tupletyp (term) (term))
  (mk-tupletyp (list (mk-tupletyp (term) (term))) (list (mk-tupletyp (type) (type))))
  );end mk-funtyp
);end

(dml |paired_form_match| 2 ml-form_match1
 (mk-funtyp 
   (mk-tupletyp (form) (form))
   (mk-tupletyp (list (mk-tupletyp (term) (term))) (list (mk-tupletyp (type) (type))))
  );end mk-funtyp
);end
