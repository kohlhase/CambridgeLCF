;******************************************************************************
;*
;*		S-gp.l
;*
;******************************************************************************
; Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile)
	 (include S-constants)
	 (include llmac)
	 (include S-macro)
         (genprefix gp)
	 (*lexpr concat))

; Manifest constants
(defvar word-sep (cascii '|%|))		; word separator for uniquesym

(de triple (x y z)  (cons x (cons y z)))  ;triple

;*****************************************************************************
;*	REVASSOC
;*****************************************************************************
; A family of "assoc" functions that match the cdr instead of the car
(de revassoc (x l)
  (tag found
       (while l
	      (let ((pair (nextl l)))
		(when (equal x (cdr pair)) (*exit found pair)))))) ; revassoc

;*****************************************************************************
;*	REVASSQ
;*****************************************************************************
(de revassq (x l)
  (tag found
       (while l
	      (let ((pair (nextl l)))
		(when (eq x (cdr pair)) (*exit found pair))))))	; revassq

;*****************************************************************************
; "assoc" functions that return only the opposite element of the pair found
(de revassoc1 (x l) (car (revassoc x l)))  ; revassoc1

(de revassq1 (x l) (car (revassq x l)))  ;revassq1

(de assq1 (x l) (cdr (assq x l)))  ; assq1

(de assoc1 (x l) (cdr (assoc x l)))  ;assoc1

(de itlist (fn xl x)
  (let ((rxl (reverse xl)))
       (while rxl (setq x (funcall fn (nextl rxl) x)))
       x))  			; itlist

(de consprop (i v p)
    (car (putprop i (cons v (get i p)) p)))  ;consprop

; duplicates ch in a list of length n
(de iterate (ch n)	
  (let ((l nil)) (while (neq n 0) (newl l ch) (decr n))	l))  ; iterate

(de can (fn args)   ;t iff fn[args] does not fail
    (tag canit
	 (tag evaluation (apply fn args) (*exit canit t))
	 nil))  ;can

(de inq (x l)
    (if (memq x l) l (cons x l)))  ;inq

(de outq (x l)
    (when l (let  ((outtail (outq x (cdr l))))
	      (if (eq x (car l)) outtail (cons (car l) outtail)))))  ; outq

(de qeval (x) (list 'quote x))  ;qeval

; Generates symbols of the form " prefix1 % prefix2 % <number> "
; These symbols may be written to the compiler output file,
;    thus they should be unique even between sessions of LCF.
; The first prefix identifies the class of the symbol
; The second prefix should contribute to uniqueness of the symbol
; The symbol count is started at a random integer [1..100].
(de uniquesym (prefix1 prefix2)
    (incr %symcount)
    (concat prefix1 '|%| prefix2 '|%| %symcount))

; initialization of uniquesym
(when initial%load (setq %symcount 0))

; Explode an atom into words separated by the "word-sep"
;   "ML % <name> % <count>" --> ("ML" <name> <count>)
; Needed to identify different kinds of uniquesyms
(de explode-word (at)
    (when (atom at)
	  (let  ((chars (nreverse (cons word-sep (exploden at))))
	         (wordlist nil))
		(while chars
		   (let ((word nil))
	       	        (while (not (eq (car chars) word-sep))
		               (newl word (nextl chars)))
			(nextl chars)
			(newl wordlist (imploden word))))
		 wordlist)))  	; explode-word

(de split (ll)
      (ifn ll (cons nil nil)
	   (let (((l1 . l2) (split (cdr ll))))
	     (cons (cons (caar ll) l1) (cons (cdar ll) l2)))))	; split

(de binarize (ll tag)
      (if ll 
        (ifn (cdr ll)
	     (car ll)
	     (list tag (car ll) (binarize (cdr ll) tag))))) ;binarize
        
(de dis-place (p1 p2)
    (rplaca p1 (car p2)) (rplacd p1 (cdr p2)))	;dis-place
; and NOT "displace" which is crazy on the Symbolics
(de putpropl (l prop)
    (mapcar '(lambda (x) (putprop (car x) (cdr x) prop)) l))	;putpropl

