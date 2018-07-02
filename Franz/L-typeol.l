;*****************************************************************************
;*
;*	TYPEOL
;*
;*****************************************************************************
; Checks types in quotations, and puts them into canonical form
; Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)
; Original : F-typeol (Cambridge LCF)

(eval-when (compile)
  (include S-constants)
  (include llmac)
  (include S-macro)
  (include L-ol-rec)
  (genprefix typeol))

(defvar %linkcount 0)

; generate a type link, an internal type variable for matching
; explicit type variables such as * are not matched
(defun genlink () (cons '%LINK (incr %linkcount)))  ;genlink

; Unify two OL types for checking types in quotations
(defun unify (ty1 ty2) (unifyb (trunc ty1) (trunc ty2)))  ;unify

; Unify "base types" -- no intervening %LINK nodes
(defun unifyb (bty1 bty2)
  (and bty1
       bty2	
       (cond
	 ((eq bty1 bty2))
	 ((is-linktype bty1) (if (occb bty1 bty2) nil (rplacd bty1 bty2)))
	 ((is-linktype bty2) (if (occb bty2 bty1) nil (rplacd bty2 bty1)))
	 ((is-vartype bty1) nil)		; since vartypes are eq
	 ((is-vartype bty2) nil)
	 ((and (eq (get-type-op bty1) (get-type-op bty2)) 
	       (forall 'unify (get-type-args bty1) (get-type-args bty2))))))
  )						;unifyb

; skip past antiquotes and resolved links in a type
(defun trunc (ty)
  (cond ((and (is-linktype ty) (not (atom (cdr ty))))  (trunc (cdr ty)))
	((is-antiquot ty) (trunc (cdr ty)))
	(ty)))					;trunc

; For unification : see if type variable v occurs in ty
(defun occ (v ty) (occb v (trunc ty)))  ;occ

(defun occb (v bty)
  (or (eq v bty)
      (selectq (type-class bty)
	((%LINK %VARTYPE %ANTIQUOT) nil)
	(t (exists '(lambda (ty) (occ v ty)) (get-type-args bty))))))	; occb

; set sticky types -- called after successful evaluation of a quotation
; Sets sticky types of all variables to their most recent type
(defun set-sticky (styl)
  (mapc 
    '(lambda (vty)
       (putprop (car vty) (q-mk_antiquot (cdr vty)) 'stickytype))
   styl)
 )			; set-sticky

; Apply sticky types to those variables whose type is still undefined
; In previous LCF, the sticky type was always used, requiring a hack
; in MK=TYPED to override it.
(defun use-sticky ()
   (mapc '(lambda (vty)
	   (let ((v (car vty)) (ty (trunc (cdr vty))))
	     (if (eq (car ty) '%LINK)
		 (rplacd ty (get v 'stickytype)))))
	 %vtyl))		; use-sticky

; Map canon-ty over all types of a formula (or term).
; Nodes from antiquotations are already in proper form.
; Retain sticky types of variables (but don't set yet)
(defun canon-quot-fm (fm)
 (selectq (form-class fm)
  (%ANTIQUOT (cdr fm))
  (pred (make-pred-form (get-pred-sym fm) (canon-quot-tm (get-pred-arg fm))))
  ((conj disj imp iff)
   (make-conn-form (get-conn fm)
        (canon-quot-fm (get-left-form fm))
	(canon-quot-fm (get-right-form fm))))
  ((forall exists)
   (make-quant-form (get-quant fm)
       (canon-quot-tm (get-quant-var fm))
       (canon-quot-fm (get-quant-body fm))))
  (t (canon-quot-tm fm))
 ))  ;canon-quot-fm

; for terms only.
(defun canon-quot-tm (tm)
 (selectq (term-class tm)
  (%ANTIQUOT (cdr tm))
  (comb
   (make-comb (canon-quot-tm (get-rator tm)) (canon-quot-tm (get-rand tm))
              (canon-ty (get-type tm))))
  (abs
   (make-abs (canon-quot-tm (get-abs-var tm)) (canon-quot-tm (get-abs-body tm))
             (canon-ty (get-type tm))))
  (var (let ((tok (get-var-name tm)) (ty (canon-ty(get-type tm))))
	 (newl %stickylist (cons tok ty)) (mk_realvar tok ty)))
  (const (ml-mk_const (get-const-name tm) (canon-ty(get-type tm))))
  (t (lcferror 'canon-quot-tm))
 ))  ;canon-quot-tm

; Strip all links from a type, complain if any are still undefined.
; To prevent expanding the DAG of links into a tree (which is exponential),
; retain before/after pairs of types in %canonlist
; Types beginning with %ANTIQUOT are already in canonical form.
(defun canon-ty (ty)
 (cond ((assq1 ty %canonlist))
   ((selectq (type-class ty)
     (%ANTIQUOT (cdr ty))
     (%LINK (if (atom (cdr ty))
		(msg-failwith '|syntax| (catenate '|canon-ty: |  "types indeterminate"))
		(canon-ty (cdr ty))))
     (%VARTYPE ty)
     (t (let ((cty (make-type (get-type-op ty)
		       (mapcar 'canon-ty (get-type-args ty)))))
	  (if (get-type-args ty) (newl %canonlist (cons ty cty)))
	  cty)))))
 )		; canon-ty

; Convert all type variables to type links
(defun omutant (ty) (let ((%tyvars nil)) (omutant1 ty)))  ;omutant

(defun omutant1 (ty)
  (if (is-vartype ty)
      (or (assq1 ty %tyvars)
	  (let ((newty (genlink))) (newl %tyvars (cons ty newty)) newty))
      (make-type (get-type-op ty)
	  (mapcar 'omutant1 (get-type-args ty)))
 ))  ;omutant1

; Functions called in ML object code

; Report errors found during evaluation of a quotation
; x is either a failure token or a list containing the quotation
(defun qtrap (x)
;the atom test is probably unneccessary!
  (if (eq (car x) 'pac);failure!
    (throw (cons (car x) (cons (cadr x) (concat (cddr x) '| in quotation|)))
     'evaluation)
    (car x)
   );end if
)  ;qtrap

; clean up a quotation
; if quotation is OK then sets sticky types and returns a singleton list.
(defun quotation (qob)
    (use-sticky)
    (let ((%stickylist nil) (%canonlist nil))
       (prog1 (list (canon-quot-fm qob))  (set-sticky %stickylist)))
   )	; quotation


