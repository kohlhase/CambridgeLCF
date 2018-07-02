;*************************************************************************r
;*
;*	L-thyfns
;*
;**************************************************************************
;* Original: F-thyfns (Cambridge LCF) 
; Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)
;  Sets Globals:  %current, %kind, %ancestry
;                 %theorydata, %theorems
;  Specials:  %e, %newtypes, %newconsts
 
(eval-when (compile)
     (include S-constants)
     (include llmac)
     (include S-macro)
     (include L-ol-rec)
     (genprefix thyfns))
 
; initialise manifests outside of initial%load
(setq dash '|-|)
(setq legalconsts '(|$| |%| |&| |+| |-| |/| |<| |=| |>| |@| |\|| |*|))
(setq %loading-thy nil)
 
 
(when initial%load				;  Globals
  (setq %current '-)				;  Settings to enable
  (setq %kind 'init)				;  pplamb in system load
  (setq %ancestry nil)
  (setq %thy-cache nil))
 
(defun defaultp (tok) (equal tok dash))
 
(defun currentp (tok) (equal tok %current))  ;currentp
 
(defun ancestorp (tok) (member tok %ancestry))  ;ancestorp
 
(defun add-ancestor (tok)
  (ifn (ancestorp tok)(newl %ancestry tok)))  ;add-ancestor
 
; Functions that produce error messages
; if no error, they return nil
 
; most are called by the theory extension functions (new_constant, ...)
; which create new theories (where %loading-thy is nil)
; and load existing ones (where %loading-thy is t)
 
(defun not-theory ()
 (ifn (eq %kind 'theory) "only allowed in a theory"))  ;not-theory
 
(defun not-draft ()
  (ifn (or %loading-thy (eq %kind 'draft))
       "Legal only in drafts")
 )  ;not-draft
 
(defun not-init ()
 (ifn (eq %kind 'init) "only allowed in new session"))  ;not-init
 
(defun neg-arity (n tok)
 (if (lessp n 0) (catenate tok " has negative arity")))  ;neg-arity
 
(defun polym (tok ty)
 (if (opoly ty) (catenate tok " would be polymorphic")))  ;polym
 
(defun not-ancestor (tok)
 (ifn (ancestorp tok) (catenate tok " is not an ancestor")))  ;not-ancestor
  
; does token consist entirely of digits?
(defun nump (tok)
 (forall '(lambda (chn) (not (or (< chn #/0) (> chn #/9))))
			   (exploden tok)))  ;nump
  
; check if the token is acceptable for the given sort
(defun bad (sort tok)
 (ifn %loading-thy
  (if (selectq sort
	(theory (not (filetokp sort tok)))
	(type  (not (idenp tok)))
	((constant infix)
	  (or (eq tok '||)
	      (not (or (eq tok '|()|) (idenp tok) (nump tok)
		       (forall '(lambda (ch) (memq ch legalconsts))
			   (explodec tok))))))
	(t nil))
    (catenate tok " cannot be " sort " token")))
 )  ;bad
 
 
; check that the given token has not already been used for the sort
; must be performed when either loading or creating a theory
(defun clash (sort tok)
   (cond
    ((selectq sort
      (theory  (fileexists 'theorydata tok))
      (type  (get tok 'olarity))
      ((constant infix)
       (setq sort
	  (cond ((get tok 'olinfix) 'infix)
		((get tok 'const) 'constant)))))
     (catenate tok " clashes with existing " sort)))
)  ;clash
 
 
(defun bad-or-clash (sort tok)
 (or (bad sort tok) (clash sort tok)))  ;bad-or-clash
 
 
(dml |new_theory| 1 ml-new_theory (mk-funtyp (string) (mk-recordtyp)))
 
; Set up lists to hold data for a draft
;   Since structures are modified destructively, "copy" is called
(defun ml-new_theory (thy)
   (cond-failwith '|theory| (bad-or-clash 'theory thy))
   (flush-draft)
   (setq %newconsts nil)
   (setq %newtypes nil)
   (setq %date (clock))
   (setq %theorydata
    (copy `((parents . ,(ifn (eq %kind 'init) (list %current)))
	    (types) (nametypes) (operators)
	    (paired-infixes) (curried-infixes) (predicates)
	    (version . ,%version)
	    (stamp . ,%date))))  ;stamp with draft-setting time
   (setq %theorems (copy '((sharetypes 0) (axiom) (fact))))
   (setq %kind 'draft)
   (add-ancestor thy)
   (setq %current thy)
   nil ; must return ni since printing of results otherwise fails (unit)
 )  ;ml-new_theory
 
 
(dml |close_theory| 1 ml-close_theory (mk-funtyp (mk-recordtyp) (mk-recordtyp)))
 
; terminate draft mode and write theory file
(defun ml-close_theory (ignore)
  (cond-failwith '|theory|  (not-draft))
  (flush-draft)
  (setq %kind 'theory)
 )				; ml-close_theory
 
 
; Add an element to a chapter of the current draft in %theorydata
; do nothing if called during loading of an existing theory
(defun add-to-chapter (sort value)
   (cond ((not %loading-thy)
       (let ((chapter (assq sort %theorydata)))
	  (rplacd chapter (cons value (cdr chapter))))))
 )  ;add-to-chapter
 
 
; Replace an existing chapter of the draft in %theorydata
(defun replace-chapter (sort value)
  (let ((chapter (assq sort %theorydata)))
   (rplacd chapter value)))  ;replace-chapter
 
 
; get a chapter of a draft or theory
(defun get-chapter (thydata sort)
    (cdr (assq sort thydata))) ; get-chapter
 
 
; Update a field of threms
(defun update-thm (threms sort factname thm)
 (let ((thl (assq sort threms)))
   (if (assoc factname (cdr thl))
     (msg-failwith '|theory| 
	(concat %failtok " " factname " clashes with existing " sort))
     (rplacd thl (cons (cons factname (encode-thm threms thm)) (cdr thl))))
 ))	; update-thm
 
 
(dml |load_theory| 1 ml-load_theory (mk-funtyp (string) (mk-recordtyp)))
 
; Load an existing theory -- must be descendant of current theory
; Must already be in some theory (possibly PPLAMBDA), not in a draft
; Allowed in init mode (the empty theory)   NEW
(defun ml-load_theory (thy)
    (let ((%failtok '|load_theory|)) (load-theory-parent thy))
    (setq %kind 'theory)
 )  ;ml-load_theory
 
 
(dml |extend_theory| 1 ml-extend_theory (mk-funtyp (string) (mk-recordtyp)))
 
; allow the user to extend an existing theory
(defun ml-extend_theory (thy)
    (let ((%failtok '|extend_theory|)) (load-theory-parent thy))
    (setq %kind 'draft)
 )  ;ml-extend_theory
 
 
(dml |new_parent| 1 ml-new_parent (mk-funtyp (string) (mk-recordtyp)))
 
; add a new parent to the current draft
(defun ml-new_parent (thy)
   (cond-failwith '|theory| (not-draft))
   (let ((%failtok '|new_parent|)) (load-theory-parent thy))
   (add-to-chapter 'parents thy))  ;ml-new_parent
 
 
; Load a theory at top-level for load_theory, extend_theory, or new_parent
(defun load-theory-parent (thy)
 (let ((prev-ancestry %ancestry)
       (%newtypes nil)
       (%newconsts nil)
       (%new-ancestors nil)
       (%loading-thy t))
  (failtrap   ; if any failure then unload the new theory
    '(lambda (errtok) (unload-theory thy prev-ancestry) 
		(msg-failwith '|theory| (concat '|theory_parent: | errtok)))
    (let ((thydata (get-thy-tree thy)))
     (cond ((member %failtok '('|load_theory| '|extend_theory|))
      (cond ((or ; check ancestry (time-stamp check suppressed)
		(eq %kind 'init)
		(member %current %new-ancestors))
	     (flush-draft)
	     (setq %date (get-chapter thydata 'stamp))
	     (setq %theorydata thydata)
	     (setq %theorems (load-theorems thy))
     	     (setq %current thy))
	    (t (msg-failwith '|theory| (concat %failtok " not a descendant of " %current))))))
   (llprinc "Theory ")(llprinc thy)(llprinc " loaded")(llterpri))))
 )  ;load-theory-parent
 
 
; The theory cache is not just for speed.
; It also avoids the need to find theory files on remote directories
; particularly PPLAMB, which is on the system builder's directory,
; and which is an ancestor of every theory.
; Eventually we will need a better treatment of remote theories
 
; an alternative is to provide a cache for time-stamps only, since we
; must always check the time-stamp of a parent, even if it is loaded already
; the parent PPLAMB is never checked anyway, since it is re-built often.
 
 
 
; update theory cache
(defun basic-update-cache (thy data)
   (if (defaultp thy) (setq thy %current))
   (let ((entry (assoc thy %thy-cache)))
    (if entry (rplacd entry data)
	(newl %thy-cache (cons thy data))))
 )				; basic-update-cache
 
 
(defun update-cache (thy thydata threms)
   (basic-update-cache thy (cons thydata threms))
 )				; update-cache
 
 
; needed after proving a theorem in a session concurrent with this one
(dml |delete_cache| 1 ml-delete_cache (mk-funtyp (string) (mk-recordtyp)))
 
(defun ml-delete_cache (thy)
   (basic-update-cache thy nil)
 )				; delete-cache
 
 
; the globals %theorydata and %theorems hold the %current theory
 
 
; open and return a channel to the theory file
; if the thy is already loaded, return (thydata . threms)
(defun open-thy-file (thy)
  (if (defaultp thy) (setq thy %current))
  (cond
    ((currentp thy) (cons %theorydata %theorems))
    ((assoc1 thy %thy-cache))
    (t (cond-failwith (concat '|theory| (not-ancestor thy)))
       (errortrap '(lambda (ertok)
		    (msg-failwith '|theory| (concat thy " theory missing")))
	   (filein (abs-path (fileof 'theorydata thy)))))
 ))				; open-thy-file
 
 
; read, reporting any errors
(defun thy-read (thy piport)
 (second	; to ignore the (quote ...) -- temporary??
  (third	; to ignore the (setq %theorydata...)
   (errortrap '(lambda (ertok) (msg-failwith '|theory| (concat %failtok thy " theory damaged")))
	(llread)))))	; thy-read
 
 
; load the given theory and return the value of its theorydata field
; does not enter into cache, since theorydata is only needed
; when first loading theory hierarchy
(defun load-theorydata (thy)
   (let ((channel (open-thy-file thy)))
    (if (consp channel) (car channel)
	(prog1 (thy-read thy channel) (close channel))
 )))		; load-theorydata
 
 
; load the given theory and return its theorems field, update cache
(defun load-theorems (thy)
   (cdr (load-thy-threms thy))
 )		; load-theorems
 
 
; load a theory and return its theorydata and theorems fields
; also save them in the cache
(defun load-thy-threms (thy)
  (let ((channel (open-thy-file thy)))
    (cond ((consp channel) channel)
	  (t (let ((thydata (thy-read thy channel)))
	       (let ((threms (thy-read thy channel)))
		  (close channel)
		  (update-cache thy thydata threms)
	          (cons thydata threms))))))
 )				; load-thy-threms
 
 
 
; load a theory hierarchy, return theorydata of root
; must return theorydata even if theory is already loaded,
; in order to check the time-stamp.
; side-effect -- store the types, constants, etc. of the hierarchy
(defun get-thy-tree (thy)
 (newl %new-ancestors thy)
 (cond ((ancestorp thy) (load-theorydata thy))
  (t
   (add-ancestor thy)
   (let ((thydata (load-theorydata thy)))
      ;parents
      (let ((%date (get-chapter thydata 'stamp)))
       (mapc 'get-parent (get-chapter thydata 'parents)))
      ;types
      (mapc '(lambda (type) (ml-new_type (car type)(cdr type)))
	     (get-chapter thydata 'types))
      ;nametypes
;     (mapc '(lambda (type) (ml-new_type_abbrev (car type)(cdr type)))
;            (get-chapter thydata 'nametypes))
      ;constants
      (mapc '(lambda (con) (ml-new_constant (car con)(cdr con)))
	    (get-chapter thydata 'operators))
      ;paired infixes
      (mapc '(lambda (infix) (ml-new_paired_infix (car infix)(cdr infix)))
	    (get-chapter thydata 'paired-infixes))
      ;curried infixes
      (mapc '(lambda (infix) (ml-new_curried_infix (car infix)(cdr infix)))
	    (get-chapter thydata 'curried-infixes))
      ;predics
      (mapc '(lambda (pred) (ml-new_predicate (car pred)(cdr pred)))
	    (get-chapter thydata 'predicates))
      thydata))))  ;get-thy-tree
 
 
; get a parent for get-thy-tree, and check its stamp
(defun get-parent (par)
    (failtrap '(lambda (errtok)	; put suffix onto any failure
		(msg-failwith '|theory| (concat errtok " ancestor " par)))
	(let ((pardata (get-thy-tree par)))))
   )				; get-parent
 
; LP -- deleted this time-stamp check from inside the "let"
; it doesn't work with extend_theory
; instead of checking the order of time stamps, it should check for an
; exact match (associate a time-stamp with each parent)
;	  (ifn (lessp (get-chapter pardata 'stamp) %date)
;	     (msg-failwith '|theory| (concat %failtok " time stamps out of sequence")))))
 
 
; An error occurred while loading theories, so undo new definitions
; It may seem cleaner to not store the constants and types until we know
;     that the load was successful, but this is impossible since loading
;     a theory requires the environment of its parents to be set up.
(defun unload-theory (tok prev-ancestry)
     (mapc 'remcon %newconsts)     ;restore constants
     (mapc 'remty %newtypes)       ;and types
     (setq %ancestry prev-ancestry)   ;and ancestors
  )  ;unload-theory
 
; Remove a type
(defun remty (tok)
  (remprop tok 'canon)
  (remprop tok 'olarity))  ;remty
 
; Remove a constant or predicate
(defun remcon (tok)
  (remprop tok 'const)
  (remprop tok 'predicate)
  (remprop tok 'olinfix)
  (remprop tok 'ol2)		; used in OL parser
  (remprop tok 'ollp))  ;remcon
 
 
; functions for building drafts
; called by get-thy-tree to load an existing theory
; or from ML to construct new draft
 
(dml |paired_new_type| 2 ml-new_type (mk-funtyp (mk-tupletyp (int) (string)) 
				     	         (mk-recordtyp)))
 
(defun ml-new_type (n tok)
  (cond-failwith '|theory| 
        (not-draft) (bad-or-clash 'type tok) (neg-arity n tok))
  (newl %newtypes tok)
  (add-to-chapter 'types (cons n tok))
  (putprop tok n 'olarity)
  (if (eq n 0) (putprop tok (cons tok nil) 'canon)))
  ;ml-new_type
 
; doesn't work for now, the nametypes are not expanded properly
; if this is re-introduced, nametypes should be expanded at parse time
; (dml new_type_abbrev 2 ml-new_type_abbrev 
;   (mk-funtyp (mk-tupletyp (string) (type)) (mk-recordtyp)))
 
;(defun ml-new_type_abbrev  (tok ty)
;  (cond-failwith '|theory| 
;       (not-draft) (bad-or-clash 'type tok) (polym tok ty))
;  (newl %newtypes tok)
;  (add-to-chapter 'nametypes (cons tok ty))
;  (putprop tok 0 'olarity)
;  (putprop tok ty 'canon)
;  (cond ((cdr ty)(putprop tok (cons (car ty) (cdr ty)) 'eqtype)
;	       (rplaca (rplacd ty nil) tok))))  ;ml-new_type_abbrev
 
;  add a new constant or predicate to the current theory
(defun add-const-pred (chap prop tok ty)
  (let ((aty (abs-type ty)))
     (newl %newconsts tok)
     (add-to-chapter chap (cons tok aty))
     (putprop tok aty prop)))   ; add-const-pred
 
 
; LP - I really don't like new_operator... how is TT an operator?
(dml |new_operator| 2 ml-new_constant 
   (mk-funtyp (mk-tupletyp (string) (type)) (mk-recordtyp)))
(dml |new_constant| 2 ml-new_constant 
   (mk-funtyp (mk-tupletyp (string) (type)) (mk-recordtyp)))
 
(defun ml-new_constant  (tok ty)
  (cond-failwith '|theory| (not-draft) (bad-or-clash 'constant tok))
  (add-const-pred 'operators 'const tok ty)
)  ;ml-new_constant
 
 
(dml |new_paired_infix| 2 ml-new_paired_infix 
   (mk-funtyp (mk-tupletyp (string) (type)) (mk-recordtyp)))
(dml |new_curried_infix| 2 ml-new_curried_infix 
   (mk-funtyp (mk-tupletyp (string) (type)) (mk-recordtyp)))
 
; Declare paired infix operator
(defun ml-new_paired_infix (tok ty)
   (cond-failwith '|theory|  (not-draft) (bad-or-clash 'infix tok))
   (ifn (and (eq (get-type-op ty) '|fun|)
	     (eq (get-type-op (first (get-type-args ty))) '|prod|))
      (msg-failwith '|theory| (concat '|new_paired_infix: | tok '| is not a function on pairs|)))
   (add-const-pred 'paired-infixes 'const tok ty)
   (olinfix tok 'paired)
  ) ;ml-new_paired_infix
 
; Declare curried infix operator
(defun ml-new_curried_infix (tok ty)
  (cond-failwith '|theory|  (not-draft) (bad-or-clash 'infix tok))
  (ifn (and (eq (get-type-op ty) '|fun|)
	    (eq (get-type-op (second (get-type-args ty))) '|fun|))
     (msg-failwith '|theory| (concat '|new_curried_infix: | tok " is not a curried function")))
  (add-const-pred 'curried-infixes 'const tok ty)
  (olinfix tok 'curried)
 ) ;ml-new_curried_infix
 
 
 
(dml |new_predicate| 2 ml-new_predicate 
   (mk-funtyp (mk-tupletyp (string) (type)) (mk-recordtyp)))
 
(defun ml-new_predicate  (tok ty)
  (cond-failwith '|theory|  (not-draft) (bad-or-clash 'constant tok))
  (add-const-pred 'predicates 'predicate tok ty)
  )  ;ml-new_predicate
 
 
 
(dml |new_open_axiom| 2 ml-new_open_axiom
   (mk-funtyp (mk-tupletyp (string) (form)) (thm)))

;(defun ml-new_open_axiom1 (factname fm)
;   (dupl_tupl (ml-new_open_axiom factname fm))
;);end
 
(defun ml-new_open_axiom  (factname fm)
   (cond-failwith '|theory|  (not-draft))
   (let ((%failtok '|new_axiom|)) (save-axiom-thm 'axiom factname fm))
)  ;ml-new_open_axiom
 
 
; cannot save theorems with assumptions, as it would be difficult
; to re-load them using the quotation mechanism
(dml |save_open_thm| 2 ml-save_open_thm
   (mk-funtyp (mk-tupletyp (string) (thm)) (thm)))

;(defun ml-save_open_thm1 (factname thm)
;   (dupl_tupl (ml-save_open_thm factname (tupl_dupl thm)))
;);end

 
(defun ml-save_open_thm  (factname thm)
  (if (get-hyp thm)
      (msg-failwith '|theory| (concat '|save_thm: | " cannot save theorems with hypotheses")))
  (let ((%failtok '|save_thm|))
     (save-axiom-thm 'fact factname (get-concl thm)))
)  ;ml-save_open_thm
 
 
; save an axiom or theorem on the current theory-draft
(defun save-axiom-thm (sort factname fm)
    (let (( (thydata . threms) (load-thy-threms %current))
	  (thm (make-thm nil (ml-rename_form fm))))
      (update-thm threms sort factname thm)
      (write-thy-file %current thydata threms)
      thm))					; save-axiom-thm
 
(dml |paired_delete_thm| 2 ml-delete_thm
   (mk-funtyp (mk-tupletyp (string) (string)) (thm)))

;(defun ml-delete_thm1 (thy factname)
 ;  (dupl_tupl (ml-delete_thm thy factname))
;);end
 
; returns the theorem, in case you delete the wrong one by mistake
(defun ml-delete_thm (thy factname)
  (if (defaultp thy) (setq thy %current))
  (let ((%failtok '|delete_thm|))
   (let  (((thydata . threms) (load-thy-threms thy)))
    (let ((thl (assq 'fact threms)))
      (let ((thpair (assoc factname (cdr thl))))
	(cond
	  (thpair
	   (delq thpair thl)
	   (write-thy-file thy thydata threms)
	   (abs-thm threms (cdr thpair)))
	  (t (msg-failwith '|theory| (concat '|delete_thm: |
		 factname " not found on theory " thy))))))))
 )	; ml-delete_thm
 
(dml |paired_axiom| 2 ml-axiom
   (mk-funtyp (mk-tupletyp (string) (string)) (thm)))

;(defun ml-axiom1 (thy factname)
;   (dupl_tupl (ml-axiom thy factname))
;);end1
 
(defun ml-axiom  (thy factname)
    (let ((%failtok '|axiom|))  (get-axiom-thm 'axiom thy factname))
 )  ;ml-axiom	
 
 
(dml |paired_theorem| 2 ml-theorem
   (mk-funtyp (mk-tupletyp (string) (string)) (thm)))

;(defun ml-theorem1 (thy factname)
;   (dupl_tupl (ml-theorem thy factname))
;);end
 
(defun ml-theorem  (thy factname)
    (let ((%failtok '|theorem|)) (get-axiom-thm 'fact thy factname))
 )  ;ml-theorem
 
 
; Get the axiom or theorem (sort) named factname from the theory thy
(defun get-axiom-thm (sort thy factname)
  (if (defaultp thy) (setq thy %current))
  (let ((threms (load-theorems thy)))
    (let ((result (assoc factname (cdr (assq sort threms)))))
	 (if result (abs-thm threms (cdr result))
	     (msg-failwith '|theory| 
              (concat %failtok " " factname " not found on theory " thy)))))
)      ; get-axiom-thm
 
 
; Re-build a theorem from its abstract form retrieved form the file
; Sets up proper internal format of variables and types
; Also links up the "sharetypes" used to save space on files
; invokes quotation system (F-typeol, F-ol-syntax)
(defun abs-thm (threms thm)
  (let ((%sharetypes (cddr (assq 'sharetypes threms))))
    (make-thm nil
     (failtrap
      '(lambda (ftok)
         (lcferror (catenate ftok " -- while reading theory file")))
       (car (let ((%vtyl nil)) (quotation (abs-form thm)))))))
 )  ;abs-thm
 
 
(dml |axioms| 1 ml-axioms
   (mk-funtyp (string) (list (mk-tupletyp (string) (thm)))))

;(defun ml-axioms1 (thy)
;   (dupl_tupl (ml-axioms thy))
;);end
 
(defun ml-axioms (thy)
  (let ((%failtok '|axioms|))  (extract-axioms-thms 'axiom thy))
)  ;ml-axioms
 
 
(dml |theorems| 1 ml-theorems
   (mk-funtyp (string) (list (mk-tupletyp (string) (thm)))))


;(defun ml-theorems1 (thy)
;   (dupl_tupl (ml-theorems thy))
;);end
 
(defun ml-theorems (thy)
  (let ((%failtok '|theorems|)) (extract-axioms-thms 'fact thy))
)  ;ml-theorems
 
 
(defun extract-axioms-thms (sort thy)
  (if (defaultp thy) (setq thy %current))
  (let ((threms (load-theorems thy)))
    (mapcar '(lambda (name-thm)
	      (list (car name-thm) (abs-thm threms (cdr name-thm))))
       (cdr (assq sort threms))))
 )      ; extract-axioms-thms
 
 
 
 
(dml |constants| 1 ml-constants 
   (mk-funtyp (string) (list (term))))
 
(defun ml-constants (thy) (extract-chapter thy 'operators))  ;ml-constants
 
 
(dml |paired_infixes| 1 ml-paired_infixes 
   (mk-funtyp (string) (list (term))))
 
(defun ml-paired_infixes (thy)
   (extract-chapter thy 'paired-infixes))  ;ml-infixes
 
 
(dml |curried_infixes| 1 ml-curried_infixes 
   (mk-funtyp (string) (list (term))))
 
(defun ml-curried_infixes (thy)
  (extract-chapter thy 'curried-infixes))  ;ml-curried_infixes
 
 
(dml |predicates| 1 ml-predicates 
   (mk-funtyp (string) (list (mk-tupletyp (string) (type)))))
 
(defun ml-predicates (thy) (dupl_tupl_l (extract-chapter thy 'predicates)))  ;ml-predicates
 
 
(dml |parents| 1 ml-parents 
  (mk-funtyp (string) (list (string))))
 
(defun ml-parents (thy) (extract-chapter thy 'parents))  ;ml-parents
 
 
(dml |types| 1 ml-types 
   (mk-funtyp (string) (list (mk-tupletyp (int) (string)))))
 
(defun ml-types (thy) (dupl_tupl_l (extract-chapter thy 'types)))  ;ml-types
 
 
 
; (defun ml-nametypes (thy) (extract-chapter thy 'nametypes))  ;ml-nametypes
 
 
(defun extract-chapter (thy kind)
  (if (defaultp thy) (setq thy %current))
  (let ((thydata (load-theorydata thy)))	; 'extract-chapter
   (let ((chapter (get-chapter thydata kind)))
      (selectq kind
	  ((parents types nametypes predicates) chapter)
	  ((operators paired-infixes curried-infixes)
	   (mapcar '(lambda (con)
		      (ml-mk_const (car con) (abs-type (cdr con))))
		    chapter))
	  (t (lcferror '(bad kind in extract-chapter)))))
   ))  ;extract-chapter
 
 
(defun flush-draft ()
  (if (eq %kind 'draft) (write-thy-file %current %theorydata %theorems))
 )				; flush-draft
 
 
; Write out theory `thy`
; First line is thydata : types, constants, infixes
; Second line is threms : axioms, facts, and sharetypes for them
(defun write-thy-file (thy thydata threms)
 (ifn (fileexists 'theorydata thy) (setq %directory "")) ;GH sets %directory
 (let ((%outport (outfile (abs-path (fileof 'theorydata thy))))
       ($gcprint nil))
      (print-file `(setq %theorydata (quote ,thydata)))
      (print-file `(setq %theorems (quote ,threms)))
      (close %outport))
 (update-cache thy thydata threms)
 )  ;write-thy-file
 
 
;Build the abstract syntax of fm s.t. fm=quotch[abs-form[fm]]
(defun abs-form (fm)
 (selectq (form-class fm)
   (conj (q-mk_conj (abs-form (get-left-form fm))
		    (abs-form (get-right-form fm))))
   (disj (q-mk_disj (abs-form (get-left-form fm))
		    (abs-form (get-right-form fm))))
   (imp (q-mk_imp (abs-form (get-left-form fm))
		  (abs-form (get-right-form fm))))
   (iff (q-mk_iff (abs-form (get-left-form fm))
		  (abs-form (get-right-form fm))))
   (forall (q-mk_forall (abs-term (get-quant-var fm))
			(abs-form (get-quant-body fm))))
   (exists (q-mk_exists (abs-term (get-quant-var fm))
			(abs-form (get-quant-body fm))))
   (pred (q-mk_pred (get-pred-sym fm) (abs-term (get-pred-arg fm))))
   (t (lcferror '(bad axiom or theorem)))))  ;abs-form
; note that in general [abs-form [quotch abs]] # abs. for instance,
; (q-mk_pair x y) becomes (q-mk_comb (q-mk_comb (q-mk_tok pair) x) y).
 
 
(defun abs-term (tm) ;builds the abstract syntax of tm
  (selectq (term-class tm)
    (var (cond-abs-type (q-mk_var (get-var-name tm)) (get-type tm)))
    (const (cond-abs-type (q-mk_const (get-const-name tm)) (get-type tm)))
    (comb (cond-abs-type
	      (q-mk_comb (abs-term (get-rator tm))(abs-term (get-rand tm)))
	      (get-type tm)))
    (abs (q-mk_abs (abs-term (get-abs-var tm))(abs-term (get-abs-body tm))))
    (t (lcferror '(bad axiom or theorem)))))  ;abs-term
 
 
; Include type if present
;   to save space, redundant types are not stored on theory files
(defun cond-abs-type (tm ty)
    (if ty (q-mk_typed tm (abs-type ty)) tm))
 
 
; build up a pplambda type, linking in %sharetypes
(defun abs-type (ty)
  (selectq (type-class ty)
    (%t (abs-type (cdr (assq (cdr ty) %sharetypes))))
    (%VARTYPE (q-mk_vartype (get-vartype-name ty)))
    (t (q-mk_type (get-type-op ty)
	    (mapcar 'abs-type (get-type-args ty))))
    ))  ;abs-type
 
 
; Encode a theorem for storage on a theory file
; throw away redundant information to save space
;   types stored in `comb` and `abs` nodes are ignored anyway
; Side-effect -- record new shared types
(defun encode-thm (threms thm)
  (let ((share (assq 'sharetypes threms)))
     (let (((%sharecount . %sharetypes) (cdr share)))
	(let ((ethm (encode-form (cadr thm))));changed cdr -> cadr
	   (rplacd share (cons %sharecount %sharetypes))
	   ethm))))   ; encode-thm
 
 
(defun encode-form (fm)
  (selectq (car fm)
     ((conj disj imp iff)
      (make-conn-form (get-conn fm)
	  (encode-form (get-left-form fm))
	  (encode-form (get-right-form fm))))
     ((forall exists)
      (make-quant-form (get-quant fm)
	    (encode-term (get-quant-var fm) t)
	    (encode-form (get-quant-body fm))))
     (pred (make-pred-form (get-pred-sym fm)
	       (encode-term (get-pred-arg fm) t)))
     (t (lcferror '(bad axiom or theorem)))))  ;encode-form
 
 
; Space reduction for terms:
;    don't write the types of "abs" and "comb" nodes
;    don't write the type of a monomorphic constant
;    share types of constants and variables
; Write type only if "needty" is true -- otherwise type is redundant
(defun encode-term (tm needty)
  (selectq (term-class tm)
    (var (let ((tok (get-var-name tm))
	       (ty (get-type tm)))
	    (make-var tok (if needty (new-sharetype tok ty)))))
    (const (let ((tok (get-const-name tm))
	         (ty (get-type tm)))
	     (make-const tok
		   (if (and needty (opoly (constp tok)))
		       (new-sharetype tok ty)))))
    (comb (encomb tm needty))
    (abs (make-abs (encode-term (get-abs-var tm) needty)
		   (encode-term (get-abs-body tm) needty)
		 nil))
    (t (lcferror '(bad axiom or theorem)))))  ;encode-term
 
 
; LP - can this be coded recursively?
; Encode a combination
; Type suppression taken from "F-writol/print-tm"
;   If the innermost rator is a polymorphic constant, don't output its type
;      instead output types of all rands and of the result type
; The type of the rator determines all the other types
(defun encomb (tm needty)
  (let ((rator tm) (rands nil) (ans nil))
    (while (eq 'comb (term-class rator))
	   (newl rands (get-rand rator))
	   (setq rator (get-rator rator)))
    (let ((pcrator (and (eq 'const (term-class rator))
		       (opoly (constp (get-const-name rator))))))
      (setq ans (encode-term rator (not pcrator)))
      (while rands
	 (setq ans (make-comb ans (encode-term (nextl rands) pcrator)
		      nil)))
      (if (and needty pcrator)
	  (put-type ans		; can we use q-mk_typed instead of update?
		  (new-sharetype (get-const-name rator)
		      (get-type tm)))))
    ans))	; encomb
 
 
; LP --  this logic should be improved or deleted!
; Put the type `ty` on the sharetypes list if:
;      the type is "big" and not shared already
; Give it a name `tok`%nnn  where `tok` is the name of the variable or const
(defun new-sharetype (tok ty)
    (if (and (bigger ty 9) (not (revassoc ty %sharetypes)))
	 (progn (let ((sharename (concat tok '% %sharecount)))
		     (incr %sharecount)
		     (newl %sharetypes (cons sharename ty)))))
    (encode-type ty))		; sharetype
 
 
; Encode a type -- copy it, using sharetypes whenever possible
(defun encode-type (ty)
  (let ((sharename (car (revassoc ty %sharetypes))))
    (if sharename (cons '%t sharename)
      (if (is-vartype ty) (q-mk_vartype (get-vartype-name ty))
	  (make-type (get-type-op ty)
		 (mapcar 'encode-type (get-type-args ty)))
	))))  ;encode-type
  
 

