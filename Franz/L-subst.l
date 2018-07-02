;**************************************************************************
;*
;*	L-subst
;*
;**************************************************************************
;* Original: F-subst (Cambridge LCF)

(eval-when (compile)
         (include S-constants)
	 (include llmac)
	 (include S-macro)
	 (include L-ol-rec)
	 (genprefix subst))



(dml |paired_aconv_form| 2 alphaconv 
   (mk-funtyp (mk-tupletyp (form) (form)) (bool)))
(dml |paired_aconv_term| 2 alphaconv 
   (mk-funtyp (mk-tupletyp (term) (term)) (bool)))


(defun alphaconv (ob1 ob2)
 (or (eq ob1 ob2)
   (let ((%varpairs nil))
     (alpha-fm ob1 ob2))))  ;alphaconv


; alpha-convertability of formulas (also passes on terms)
(defun alpha-fm (fm1 fm2)
   (and (eq (form-class fm1)(form-class fm2))
     (selectq (form-class fm1)
	((forall exists)
	  (let ((%varpairs (cons (cons(get-quant-var fm1)(get-quant-var fm2))
				 %varpairs)))
	     (alpha-fm (get-quant-body fm1)(get-quant-body fm2))))
	((conj disj imp iff)
	    (and (alpha-fm (get-left-form fm1)(get-left-form fm2))
	         (alpha-fm (get-right-form fm1)(get-right-form fm2))))
	(pred (and (eq (get-pred-sym fm1) (get-pred-sym fm2))
		   (alpha-tm (get-pred-arg fm1)(get-pred-arg fm2))))
	(t (alpha-tm fm1 fm2))
 )))  ;alpha-fm


; alpha-convertability of terms
(defun alpha-tm (tm1 tm2)
  (and (eq (term-class tm1)(term-class tm2))
     (selectq (term-class tm1)
        (const (equal tm1 tm2))   		; assumes sharing of constants
	(var	; if either bound then bindings must match
		; free case assumes variables are shared
	      (let ((p1 (assoc tm1 %varpairs))
		    (p2 (revassq tm2 %varpairs)))
		(if (or p1 p2)(eq p1 p2) (eq tm1 tm2))))
	(abs
	  (let ((%varpairs (cons (cons(get-abs-var tm1)(get-abs-var tm2))
				 %varpairs)))
	     (alpha-tm (get-abs-body tm1)(get-abs-body tm2))))
	(comb (and (alpha-tm (get-rator tm1)(get-rator tm2))
	           (alpha-tm (get-rand tm1)(get-rand tm2))))
	(t (lcferror 'alpha-tm))
 )))  ;alpha-tm



; *********************************************


(dml |term_frees| 1 freevars 
   (mk-funtyp (term) (list (term)))) 
(dml |form_frees| 1 freevars 
   (mk-funtyp (form) (list (term))))

(defun freevars (ob)
       (let ((%all nil)(%vars nil))
	  (vars-fm ob nil)
	  (nreverse %vars)))  ;freevars


(dml |term_vars| 1 allvars 
   (mk-funtyp (term) (list (term)))) 
(dml |form_vars| 1 allvars 
   (mk-funtyp (form) (list (term))))

(defun allvars (ob)
       (let ((%all t)(%vars nil))
	  (vars-fm ob nil)
	  (nreverse %vars)))  ;allvars


; record the variables in a formula (or term)
; if %all then record all variables, even those bound but never used
; else record only free variables
(defun vars-fm (fm bvars)
 (selectq (form-class fm)
   ((forall exists)
      (if %all (addvar (get-quant-var fm)))
      (vars-fm (get-quant-body fm) (cons (get-quant-var fm) bvars)))
   ((conj disj imp iff)
    (vars-fm (get-left-form fm) bvars) (vars-fm (get-right-form fm) bvars))
   (pred (vars-tm (get-pred-arg fm) bvars))
   (t (vars-tm fm bvars))))  ;vars-fm


; record all (free) variables in a term
(defun vars-tm (tm bvars)
 (selectq (term-class tm)
   (const)
   (var (ifn (member tm bvars) (addvar tm)))
   (abs (if %all (addvar (get-abs-var tm)))
	(vars-tm (get-abs-body tm) (cons (get-abs-var tm) bvars)))
   (comb (vars-tm (get-rator tm) bvars) (vars-tm (get-rand tm) bvars))
   (t (lcferror 'vars-tm))))  ;vars


; record a variable if not seen already
; relies on sharing of variables
(defun addvar (v)
    (ifn (member v %vars) (newl %vars v)))  ;addvar



; *********************************************


(dml |paired_subst_term| 2 substitute
 (mk-funtyp (mk-tupletyp (list (mk-tupletyp (term) (term))) (term)) (term)))

(dml |paired_subst_form| 2 substitute
  (mk-funtyp (mk-tupletyp (list (mk-tupletyp (term) (term))) (form)) (form)))

(dml |paired_subst_occs_term| 3 substitute-occs
  (mk-funtyp (mk-tupletyp (list (list (int)))
		          (list (mk-tupletyp (term) (term)))
			  (term))  (term)))

(dml |paired_subst_occs_form| 3 substitute-occs
  (mk-funtyp
	(mk-tupletyp
		(list (list (int)))
		(list (mk-tupletyp (term) (term)))
		(form)
	);end mk-tuple
	(form)
    );end	
);end


(defun substitute (jobl ob)
 (let ((%newvars nil))
   (subst-fm (mapcan '(lambda (job) (substrec t job)) jobl) ob))
 )   ; substitute


(defun substitute-occs(occsl jobl ob)
  (let ((%newvars nil))
     (ifn (eq (length occsl) (length jobl))
	  (msg-failwith '|syntax| '|substitution|))
     (subst-fm(mapcan 'substrec occsl jobl) ob))
 )   ; substitute-occs


(defmacro get-term1 (sr) `(car ,sr))
(defmacro get-term2 (sr) `(cadr ,sr))
(defmacro get-occs (sr) `(caddr ,sr))
(defmacro get-frees1 (sr) `(cadddr ,sr))
(defmacro get-frees2 (sr) `(car (cddddr ,sr))) ;gh

(defmacro put-occs (sr val) `(rplaca (cddr ,sr) ,val))


; preprocess a substitution
; check types, compute free variables, set up occurrence lists
; return a record holding this info
; return nil if substitution is null
; for use with mapcan (NOT mapcar!)
(defun substrec(occs job)
   (let ((tm2 (car job)) (tm1 (cadr job)))
    (ifn (equal (get-type tm1) (get-type tm2)) 
		(msg-failwith '|syntax| '|substitution|))
    (ifn (eq tm2 tm1)
      (ncons (list tm1 tm2 (occrec 1 occs) (freevars tm1) (freevars tm2)))))
 )   ; substrec


; convert an ascending list of positive integers
; into a list of nil's, with t's interspersed where the integers indicate
(defun occrec(n l)
 (cond
  ((atom l) (twistlist l))	; extend out to infinity
  ((greaterp n (car l)) (msg-failwith '|syntax| '|substitution|))  
; not ascending
  ((eq n (car l)) (cons t (occrec (add1 n)(cdr l))))
  ((cons nil (occrec (add1 n) l)))
))


; substitute in a formula (or term)
(defun subst-fm (srl fm)
 (cond ((and (null srl) (null %newvars)) fm)
  ((selectq (form-class fm)
    ((forall exists) (quant-sub srl fm))
    ((conj disj imp iff)
     (make-conn-form (get-conn fm)
	 (subst-fm srl (get-left-form fm))
	 (subst-fm srl (get-right-form fm))))
    (pred (make-pred-form (get-pred-sym fm)
	      (subst-tm srl (get-pred-arg fm))))
    (t (subst-tm srl fm))))))  ;subst-fm


; substitute in a term
(defun subst-tm (srl u)
 (cond ((and (null srl) (null %newvars)) u)
  ((find-sub srl u))
  ((selectq (term-class u)
    (const u)
    (var (or (assq1 u %newvars) u))	; rename bound variable
    (abs (abs-sub srl u))
    (comb (make-comb (subst-tm srl (get-rator u))
	      (subst-tm srl (get-rand u)) (get-type u)))
    (t (lcferror 'subst-tm))))))  ;subst-tm


; base case of substitution
; if match found, step down its occurrence list
;   and return non-nil even if this occurrence is not included
; return nil if no match
(defun find-sub(srl u)
  (tag found
   (mapc '(lambda (sr)
	   (let ((tm1 (get-term1 sr)) (tm2 (get-term2 sr)))
	    (if (alphaconv u tm1)	; match found
		(let ((occs (get-occs sr)))
		   (put-occs sr (cdr occs))
		   (*exit found (if (car occs) tm2 u))))))
	  srl)
    nil		; indicate not found
 ))    ; find-sub



; substitution through a bound variable
;   if var could be introduced, then rename it
(defun quant-sub (srl fm)
 (let ((var (get-quant-var fm)) (body (get-quant-body fm)))
  (let ((new-srl (varfilter var srl)))
    (let ((new-var (choose-var new-srl var body)))
        (let ((%newvars (cons (cons var new-var) %newvars)))
           (make-quant-form (get-quant fm)
               new-var (subst-fm new-srl body))))))
 )    ; quant-sub


; substitute through a lambda-abstraction
(defun abs-sub (srl tm)
 (let ((var (get-abs-var tm)) (body (get-abs-body tm)))
  (let ((new-srl (varfilter var srl)))
    (let ((new-var (choose-var new-srl var body)))
        (let ((%newvars (cons (cons var new-var) %newvars)))
           (make-abs new-var (subst-tm new-srl body) (get-type tm))))))
 )    ; abs-sub


; filter (from the srl) all rewrites where the var is free
; since substitution replaces only free terms
(defun varfilter (var srl)
 (if srl
   (if (memq var (get-frees1 (car srl)))
       (varfilter var (cdr srl))
       (cons (car srl) (varfilter var (cdr srl))))
 ))   ; varfilter


; choose a new bound variable if old one is mentioned in rewrites
; RECENT BUG FIX -- now considers any new variables being introduced
; as a result of outer name clashes
; #let tm = "\x':*.f (y:*,z:*) (\x:*.(g (x',x,y,z) : tr) ):tr";;
; #let tm1 = subst_term ["x'","z"; "x","y"] tm;;
; SHOULD GIVE  tm1 = "\x''.f(x,x')(\x'''.g(x'',x''',x,x'))" : term
(defun choose-var (srl var body)
   (let ((frees2 (append (mapcar 'cdr %newvars) (all-frees2 srl))))
      (if (memq var frees2)
	  (ml-variant (nconc (allvars body) frees2) var)
	  var)))


; union of all frees2 fields of srl
(defun all-frees2 (srl)
   (if srl (append (get-frees2 (car srl)) (all-frees2 (cdr srl))))
 )    ; all-frees2



; *********************************************


(dml |paired_term_freein_term| 2  freein-tm 
  (mk-funtyp (mk-tupletyp (term) (term)) (bool)))
(dml |paired_term_freein_form| 2  freein-fm 
  (mk-funtyp (mk-tupletyp (term) (form)) (bool)))
(dml |paired_form_freein_form| 2  freein-fm 
   (mk-funtyp (mk-tupletyp (form) (form)) (bool)))

; in the current logic, formulas cannot occur in terms
; but in general, all four cases are reasonable,
; and it is convenient to define freein in terms of "objects",
; where objects are either terms or formulas.




; see if the ob is free in a formula (or term)
(defun freein-fm (ob fm)
  (or (alphaconv ob fm)
   (selectq (form-class fm)
    ((forall exists)
     (and (not (freein-fm (get-quant-var fm) ob))
	  (freein-fm ob (get-quant-body fm))))
    ((conj disj imp iff)
     (or (freein-fm ob (get-left-form fm))
	 (freein-fm ob (get-right-form fm))))
    (pred (freein-tm ob (get-pred-arg fm)))
    (t (freein-tm ob fm))
 )))  ;freein-fm



; see if the ob is free in a term
(defun freein-tm (ob tm)
  (or (alphaconv ob tm)
   (selectq (term-class tm)
    ((var const) nil)
    (abs (and (not (freein-tm (get-abs-var tm) ob))
	      (freein-tm ob (get-abs-body tm))))
    (comb (or (freein-tm ob (get-rator tm)) (freein-tm ob (get-rand tm))))
    (t (lcferror 'freein-tm))
 )))  ;freein-tm




; *********************************************


(dml |paired_variant| 2 ml-variant 
  (mk-funtyp (mk-tupletyp (list (term)) (term)) (term)))


; prime v until its name is neither a constant's nor one of the vl
(defun ml-variant (vl v)
  (ifn (memq (term-class v) '(var const))  (msg-failwith '|syntax| '|variant|) )
  (let ((tokl  (var-name-list vl 'variant)))
    (mk_realvar (variant-name tokl (get-var-name v)) (get-type v)))
)  ;ml-variant


; get the names of the list of variables
(defun var-name-list (vl failtok)
 (mapcar '(lambda (tm) (if (is-var tm) (get-var-name tm)
		       (msg-failwith '|syntax| failtok)))
	 vl))			; var-name-list


; prime tok until it is neither a constant's name nor one of the tokl
; no longer strips primes first, that caused problems in ML programs
(defun variant-name (tokl tok)
  (while (or(memq tok tokl)(constp tok)) (setq tok (prime tok)))
  tok)  ; variant-name


(defun prime (tok) (concat tok '|'|))  ;prime


; strip all primes from tok (including those inside)
(defun unprime (tok) (imploden (delq #/' (exploden tok))))  ;unprime


