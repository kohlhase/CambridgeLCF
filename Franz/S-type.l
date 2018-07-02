;*****************************************************************************
;*
;*	S-type.l
;*
;*****************************************************************************
; SML type checker
; Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile)
(include S-constants)
(include llmac)
(include S-macro))

;set of functions whose args must be of type num (real or int)
(defconst num_ops '(|~| |abs| |*| |+| |-| ))

;set of functions whose args must be of type nums (num or string)
(defconst nums_ops '(|<| |>| |<=| |>=|))

;*****************************************************************************
;*	Useful Functions
;*****************************************************************************


;*****************************************************************************
;*	TYPECH_FAILED
;*****************************************************************************
(de typech_failed (msg)
   (llprinc msg)
    (llterpri)
    (*exit typecheck nil)
);end typech_failed

;*****************************************************************************
;*	OK_DEP
;*****************************************************************************
;check for each tycon in tycondep_l that tycon is not in noneq_l.
;where noneq_l is a list of tycons that do not admit equality.
(de ok_dep (noneq_l tycondep_l)
   (cond
	((null tycondep_l) t)
	((memq (car tycondep_l) noneq_l) nil);check if first tycon admits eq
	(t (ok_dep noneq_l (cdr tycondep_l)))
   );end cond
);end ok_dep

;*****************************************************************************
;*	TYCON_ADMITS_EQ
;*****************************************************************************
;check if tycon admits equality (called from datatype_typing)
(de tycon_admits_eq (ty tycon_l noneq_l)
   (cond
	((mlink ty));type variable ok!
	((eq (car ty) 'mk-recordtyp);check each element
		(exists 
		   '(lambda (x) (tycon_admits_eq (cdr x) tycon_l noneq_l))
		    (cdr ty)
		));end exists
	((eq (car ty) 'mk-tupletyp)
	   (exists 
		'(lambda (x) (tycon_admits_eq x tycon_l noneq_l))
		 (cdr ty)
	   ));end exists
	((eq (car ty) 'mk-funtyp) nil);funtyp does not admit equality!
	(t; unique symbols
	   (cond
		((memq (car ty) noneq_l) nil);
		((memq (car ty) tycon_l) t);tycons declared concurrently
			;are all asumed to admit equality initially	
		((get (car ty) 'equality));declared previously!
	   ));end cond
   );end cond
);end admit_eq

;*****************************************************************************
;*	ASSQTIDY1
;*****************************************************************************
;assq1 but tidy first
(de assqtidy1 (ty generic)
   (cond
	((null generic) nil)
	((eq ty (prune (caar generic))) (cdar generic))
	(t (assqtidy1 ty (cdr generic)))
   );end cond
);end assqtidy1
	   
;*****************************************************************************
;*	ADMIT_EQUALITY
;*****************************************************************************
;check if ty admits equality
(de admit_equality (ty)
   (cond
	((mlink ty) nil);type variable not admited
	((eq (car ty) 'mk-funtyp) nil);same for fun typ
	((eq (car ty) 'mk-recordtyp);check each component
	       (exists
		   '(lambda (x) (admit_equality (cdr x)))
		    (cdr ty)
		));end exists
	((eq (car ty) 'mk-tupletyp)
	   (exists 'admit_equality (cdr ty)))
	(t;unique symbol
	   (if (get (car ty) 'equality);equality property set in concrete_type
		(if (cdr ty);instantiated type variables?
		   (exists 'admit_equality (cdr ty)) 
		   t;else t
		);end if
	    ));end if
   );end cond
);end admit_equality

;***************************************************************************
;*        SPLIT_AND
;***************************************************************************
(de split_and (l)
      (ifn l (cons nil nil)
	   (let (((l1 . l2) (split_and (cdr l))))
	     (cons (cons (cadar l) l1) (cons (caddar l) l2))
	   );end let   
      );end ifn
);end split_and

;*****************************************************************************
;*	IS_OVERLOAD
;*****************************************************************************
;true if id is an overloaded function
(de is_overload (id)
   (ifn (is_inenv id env) ;ifn redefined:
	(get id 'overload))
);end is_overload

;*****************************************************************************
;*	IS_INENV
;*****************************************************************************
;true if id is in env (env is list of A-lists)
(de is_inenv (id env)
   (cond
	((null env) nil)
	((assoc id (cdar env)))
	(t (is_inenv id (cdr env)))
    );end cond
);end is_env

;***************************************************************************
;*        TYPE_BINDINGS
;***************************************************************************
;*
;*DESCRIPTION: Add new layer to the environment tenv.
;*
;*****************************************************************************
(de typebindings (l) (newl tenv l))		;typebindings

;***************************************************************************
;*        GENMLINK
;***************************************************************************
;*
;*DESCRIPTION: Generate a type variable.
;*
;***************************************************************************
(de genmlink (p) (ncons p));end genmlink

;***************************************************************************
;*        STRUCTOFF
;***************************************************************************
(de structoff (x) (setq structcheck nil) x)

;***************************************************************************
;*       STRUCTON 
;***************************************************************************
;*
;*DESCRIPTION: structcheck set to t when typechecking patterns.
;*
;*****************************************************************************
(de structon (x) (setq structcheck t) x)

;***************************************************************************
;*       POPENV 
;***************************************************************************
;*
;*DESCRIPTION: pop top layer on env and return x.
;*
;***************************************************************************
(de popenv (x) (nextl env) x)

;***************************************************************************
;*        TWISTLIST
;***************************************************************************
;*
;*DESCRIPTION: Make a circular list (x x x ... )
;*
;***************************************************************************
(de twistlist (x) (let ((lx (list x))) (rplacd lx lx)))


;***************************************************************************
;*        EXPAND_TYPE
;***************************************************************************
;*
;*DESCRIPTION: expand type abbrevations (also called from S-tran)
;*
;***************************************************************************
;flg=t indicates that type_l is a list of intern. repr. of types
;t=nil : type_l is list of parse trees of type expressions
(de expand_type (abbtyp tyv_l type_l flg)
	(let ((par_l (combinetyp tyv_l type_l flg))) ;build up assoc. list
		(expand_type1 abbtyp par_l)
	);end let
);end expand_type

;***************************************************************************
;*       EXPAND_TYPE
;***************************************************************************
(de expand_type1 (abbtyp par_l) ;abbtyp is abbrevation with type variables(if any)
   (cond			;par_l is list of type parameters
        ((null abbtyp) nil)
	((eq (car abbtyp) 'mk-recordtyp); ignore labels!
	   (cons (car abbtyp); changed to abbtyp 15/3/87
		(mapcar
		   '(lambda (x) (cons (car x) (expand_type1 (cdr x) par_l)))
		    (cdr abbtyp)
		);end mapcar
	   ));end cons
	((atom abbtyp) abbtyp); 
	((mlink abbtyp); explicit type variable !
	   (assoc1 (car abbtyp) par_l));replace tyvar with type in par_l!
	(t 
	   (cons 
		(expand_type1 (car abbtyp) par_l) 
	        (expand_type1 (cdr abbtyp) par_l)))
   );end cond
);end expand_type1

;*****************************************************************************
;*	COMBINETYP
;*****************************************************************************
;combine tyl and tyl2 to a list of lisp-pairs.
(de combinetyp (tyl1 tyl2 flg)
   (cond
	((null tyl1) nil)
;if flg=t then tyl2 is parse tree of type expression.
	((atom tyl1) (cons tyl1 (if flg tyl2 (typing tyl2))))
	(t 
	   (cons 
		(combinetyp (car tyl1) (car tyl2) flg)
		(combinetyp (cdr tyl1) (cdr tyl2) flg)
	   ));end cons
    );end cond
);end combinetyp

;*****************************************************************************
;*	TIDY
;*****************************************************************************
;*
;*DESCRIPTION: give type variables (implicit) tyvar names
;*	       starting with 'a and then 'b, 'c ...
;*
;*****************************************************************************
(de tidy (ty) (let ((%l nil) (%star (cascii "a"))) (tidyup ty)))

;***************************************************************************
;*        TIDYCDRS
;***************************************************************************
(de tidycdrs (l)
    (mapc '(lambda(x) (rplacd x (tidy (cdr x)))) l))	;tidycdrs

(de tidy1 (ty) (let ((tenv %temt)) (tidy ty)))	;tidy1  

;*****************************************************************************
;*	TIDYUP
;*****************************************************************************
(de tidyup (ty)
    (cond
      ((eq (car ty) 'mk-decseqtyp)
	  (cons (car ty)
	    (mapcar 'tidy (cdr ty))
	  ));end cons
      ((memq (car ty) '(mk-recordtyp mk-wildrecordtyp))
	 (cons (car ty)
	   (mapcar
		'(lambda (x) (cons (car x) (tidyup (cdr x))))
		 (cdr ty)
	   );end mapcar
	));end cons
      ((instof ty) (tidyup (instof ty)))
      ((assq1 ty %l))
      ((mlink ty);implicit or explicit type variable
	(if (is_type_var (car ty)) ty; return explicit tyvar
	;else
	    (cond
		((assqtidy1 ty %generic));non-instatiated generic. tyvar
		(t;implicit type variable
		  (let ((tyv `(,(concat "'" (ascii %star)))))
		    (while (revassoc tyv %generic);don't use generic type vars
			(setq tyv `(,(concat "'" (ascii (incr %star)))))
		    );end while
		    (incr %star)
		    (newl %l (cons ty tyv))
		    tyv));end let
	     );end cond
	  ));end if
      ((cons (car ty) (mapcar 'tidyup (cdr ty))))
   );end cond
);tidyup


;*****************************************************************************
;*	FIND_MISSING_LAB
;*****************************************************************************
;*
;*DESCRIPTION: Search for missing labels in numeric records.
;*
;*****************************************************************************
(de find_missing_lab (c)
  (if (and (num_labp (caadr c)) (cdr c)); empty record or num. labels
   (ifn
     (and (eq (value (getcharn (caadr c) 1)) 1)
	 (eq (length (cdr c))
	  (+ 1
	    (- (value (getcharn (last_label (cdr c)) 1))  1)))
      );end and
       (typech_failed '|record/record type: missing numeric label |)
	c;
   );end ifn
   c;
  );end if
);end find_missing_lab

;*****************************************************************************
;*	LAST_LABEL
;*****************************************************************************
(de last_label (c)
   (cond
	((eq (length c) 1) (caar c))
	(t (last_label (cdr c)))
   );end cond
);end last_label

;*****************************************************************************
;*	SORT_RECORD
;*****************************************************************************
;*
;*DESCRIPTION: Sort a numeric record in alphanumeric order.
;*
;*****************************************************************************
(de sort_record (c)
  (if (and (num_labp (caadr c)) (cdr c));empty record or id labels
   (cons (car c)
	(sort (cdr c) '(lambda (x y) (alphalessp (car x) (car y))))
   );end cons
   c;
 );end if
);end sort_record

;*****************************************************************************
;*	FILL_RECORD
;*****************************************************************************
;*
;*DESCRIPTION: Fill up the places in a numeric record where labels are
;*	       "missing". 
;*		(label . (%mlink)) - flg=t
;*		(label . (mk-wildcard)) - flg=nil
;*
;*	        - also called by "varpat" in tran.l. (flg=nil)
;*****************************************************************************
(de fill_record (c flg)
 (if (num_labp (caadr c)); empty record or num. labels
     (if 
	      (> (lab_val (caadr c)) 1);if 1st label> 1, insert 1st lab.
	(cons (car c)
	    (fill_record1
		`(,(concat 1) . ,(if flg (genmlink '%MLINK) '(mk-wildcard)))
		 (cdr c)
		  flg
	    );end fill_record1
	);end cons
   	(cons (car c) (fill_record1 (cadr c) (cddr c) flg))
      );end if
      c;
  );end if
);end fill_record

;*****************************************************************************
;*	FILL_RECORD1
;*****************************************************************************
(de fill_record1 (i l flg)
   (cond
	((null l) 
	      `(,i))
	((eq (lab_val (caar l));
	     (+ (lab_val (car i)) 1)); no labels missing
	   (cons i (fill_record1 (car l) (cdr l) flg )))
	(t; labels missing, fill out with (%MLINK) or (mk-wildcard)
	   (cons i 
	     (fill_record1 ;add new layer
		`(,(concat (+ (lab_val (car i)) 1)) . 
			,(if flg (genmlink '%MLINK) '(mk-wildcard)))
		 l;
		 flg
	     );end fill_record
	   ));end cons
   );end cond
);end fill_record

;*****************************************************************************
;*	REMOVE_LAB
;*****************************************************************************
;remove labels in record
(de remove_lab (l)
   (mapcar `(lambda (x) (cdr x)) l)
);end remove_lab

;*****************************************************************************
;*	ADD_RECLAY
;*****************************************************************************
;*
;*DESCRIPTION: Fill up a wild record record with the label-item pairs that are
;*	       missing (if any) when unifying with numeric record
;*
;*****************************************************************************
(de add_reclay (l n)
   (let ((x (- n (length l))))
      (if (plusp x)
 	(while x
	   (newr l (genmlink '%MLINK));generate implicit tyvar
	   (setq x (sub1 x))
	);end while
      );end if
      l; return l
   );end let
);end add_reclay

;*****************************************************************************
;*	LAB_VAL
;*****************************************************************************
;returns the value of a numeric label
(de lab_val (lab)
   (let ((n 2) (x nil) (accu (value (getcharn lab 1))))
 	(while (setq x (getcharn lab n))
	   (setq accu (+ (* accu 10) (value x)))
	   (incr n)
	);end while
	accu;return accu
   );end let
);end lab_val

;*****************************************************************************
;*	NUM_LABP
;*****************************************************************************
;true if record have numeric labels
(de num_labp (t)
  (prog (x)
   (return (and (> (setq x (getcharn t 1)) 47)
	(< x 58)))
  );end prog
);end num_labp

;*****************************************************************************
;*	REMOVE_LAY
;*****************************************************************************
;remove a label-item pair from record.
(de remove_lay (i l)
   (cond 
	((eq i (caar l))
  	   (cdr l))
	(t (cons (car l) (remove_lay i (cdr l))))
   );end con
);end remove_lay

;*****************************************************************************
;*	MAKETY
;*****************************************************************************
;used in dml.l
(de makety (ty)
   (cond
  	((null ty) nullty)
 	((atom ty) (make_atom_ty ty))
	((eq (cadr ty) 'list)
	   (list 'mk-listtyp (makety (car ty))))
	((eq (cadr ty) arrow_sym)
	   (list 'mk-funtyp (makety (car ty)) (makety (caddr ty))))
	((eq (cadr ty) mul_sym)
	   (list 'mk-tupletyp (makety (car ty)) (makty (caddr ty))))
   );end cond
);end makety

;*****************************************************************************
;*	MAKE_ATOM_TY
;*****************************************************************************
(de make_atom_ty  (ty)
   (selectq ty
	(|unit| unittyp)
	(|int| inttyp)
	(|real| realtyp)
	(|bool| booltyp)
	(|string| stringtyp)
   );end selectq
)

;*****************************************************************************
;*	MULT_OCC
;*****************************************************************************
;*
;*DESCRIPTION: Check for multiple occurence of identifier in pattern.
;*
;*****************************************************************************
(de mult_occ (pat)
   (let ((%mult_l nil))
	(mult_occ1 pat)
   );end let
);end mult_occ

(de mult_occ1 (pat)
   (selectq (car pat)
      	(mk-wildcard)
        ((mk-con mk-opcon mk-const mk-opconst) nil)
      	((mk-var mk-opvar )
	   (if (memq (cadr pat) %mult_l);check if id is already used.
		(typech_failed
		   (concat
		'|pattern: multiple occurrence of identifier - |
			(cadr pat)))
		(newl %mult_l (cadr pat));not used, add to %mult_l
	   ));end if
	 ((mk-record mk-wildrecord)
	   (mapc; check for each label-item pair in the record
	  	'(lambda (x) (mult_occ1 (cdr x)))
		(cdr pat)
	   ));end mapcar
	((mk-tuple mk-list mk-appn mk-infappn mk-laypat);
		;check for constant in appl.
	   (if (and (memq (car pat) '(mk-appn mk-infappn))
		    (eq (caadr pat) 'mk-const))
		(typech_failed
		  (concat
		  '|pattern: bad constructor used in application: |
			(cadadr pat)))
	    );end if
	   (mapc 'mult_occ1 (cdr pat)))
	(mk-straint (mult_occ1 (cadr pat)))
   );end selectq
);end mult_occ

;***************************************************************************
;*        NEWDEFTYPE
;***************************************************************************
(de newdeftype (id tyx)
   (let ((ty (typing tyx)))
	    (cons id (tidy ty))
    );end let
);end newdeftype

;***************************************************************************
;*        TYPING
;***************************************************************************
;*
;*DESCRIPTION: infer type for ml-construction.
;*
;*LOCAL VARIABLES: mark : marker, eg. mk-intconst, mk-realconst ...
;*		     tl : tail of parse tree.
;*		     ty, ty$ : generated implicit type variables.
;*
;***************************************************************************
(de typing (p_tree)
   (let ((mark (car p_tree)) (tl (cdr p_tree)) (ty (genmlink '%MLINK))
	(ty$ (genmlink '%MLINK)))
	(selectq mark

	   (mk-empty unittyp)
	   (mk-intconst (typing inttyp))
	   (mk-boolconst (typing booltyp))
	   (mk-realconst (typing realtyp))
	   (mk-stringconst (typing stringtyp))

	   (mk-wildcard 
		(if structcheck ; pattern ?
			(genmlink '%MLINK)
			(llprinc `|wildcard can only be used in patterns|)
			(llterpri)
			(*exit typecheck nil)
		);end if
	   );end mk-wildcard

	   (mk-funtyp 
		(cons mark (mapcar `typing tl)))


	   (mk-vartyp
	      (let ((ty (genmlink (car tl))));generate explicit tyvar
		(cond
		   ((assoc1 (car tl) %vartypes));already used ?
		   ((newl %vartypes (cons (car tl) ty)) ty)
		);end cond
	      );end let
	   );end mk-vartyp

	   (mk-recordtyp 
	     (let ((ty
		(find_missing_lab;search for missing labels (if numeric)
		   (sort_record
			(cons mark
			   (mapcar; deduce type for each label-item pair!
			     '(lambda (x) (cons (car x) (typing (cdr x))))
			      tl;
			   );end mapcar
			);end cons
		    );end sort_record
		);end fin_label
	             ));end ty
		;if numeric label and no of components>1 : treat as mk-tupletyp
		(if  (num_labp (caar tl)) 
		     (cons 'mk-tupletyp
			(mapcar 'cdr (cdr ty))
		     );end cons
		     ty
		 );end if
	      );end let
	  );end mk-recordtyp

	   (mk-tupletyp;
		(cons mark
		   (mapcar 'typing  tl)
		);end cons
	   );end tupletyp


	   (mk-consttyp; type constructor. 

		(cond
		   ((get (gettypet (car tl)) 'abbrevtyp) ;abbrevation
			(if (checktype tl); check that no. of type par. is corr.
		          (let ((ty (get (gettypet (car tl)) 'abbrevtyp))
				(tyv_l (get (gettypet (car tl)) 'tyvarl)))
				;expand rhs of tycons' binding	
			     (expand_type ty tyv_l (cdr tl) nil)
			  );end let
			;else abbrevation without tyvars!
		          (typing (get (gettypet (car tl)) 'abbrevtyp) )
			 ));end if
		   (t ; datatype construction.
			(if (checktype tl)
			   (cons (gettypet (car tl));get unique symbol!
				 (mapcar 'typing (cdr tl))
			   );end cons
			   (gettypet (car tl))
			));end if
		);end cond
	   );end mk-consttyp


	   ((mk-var mk-opvar) 
;for all overloaded functions, the type of the argument is communicated to
;the translator by inserting the type (in place) in the prsee tree:
; (mk-var print) becomes (mk-var print %mlink int) for example!
	      (let ((ty (getid_typ (car tl) 'var)))
		  (cond
			((is_overload (cadr p_tree));if id is an overloaded fn:
			   (let ((checkty
		;pick out type of argument (abs and ~ are unary) !
				(if (memq (cadr p_tree) `(abs ,neg_sym))
					(cadr ty) (cadadr ty)
				)));end if
			       (newl %overload (cons (cadr p_tree) 
				  checkty);save for later check
				);end newl
			       (rplacd (cdr p_tree) checkty);add ty to parsetree.
			   ));end let
	 	;include type in parse_tree
		         ((eq (cadr p_tree) 'makestring)
				(newl %monotypes (cons 'makestring (cadr ty)))
				(rplacd (cdr p_tree) (cadr ty)))
		;argument for print must be monotype:
			 ((eq (cadr p_tree) 'print)
			    (newl %monotypes (cons 'print (cadr ty)))
			    (rplacd (cdr p_tree) (cadr ty)))
		  ;argument for assignment op. must be monotype
		         ((eq (cadr p_tree) assign_sym)
			    (newl %monotypes (cons '|:=| (cadadr ty))))

		         ((memq (cadr p_tree) `(,eq_sym ,neq_sym))
		  ;types of the args to "=" and "<>" must be checked (ety)
		  ;note: we use the same criteria for print!
			    (newl %eqtypes (cons (cadadr ty) (cadr p_tree)))
			    (rplacd (cdr p_tree) (cadadr ty)))
		  );end cond
		  ty; return ty
		);end let
	   );end mk-var

	   ((mk-con mk-opcon mk-const mk-opconst) 
		(let ((ty (getid_typ (car tl) 'con)))
			(if %eq_flg1 ; typing lhs of equality ?
			;%coneq_l is used in translator
			;to choose correct equality func. for con!
				(newr %coneq_l ty)
			);end if
			ty;return ty
		);end let
	   );end mk-con

	   (mk-infappn
		(typing `(mk-appn ,(car tl) (mk-tuple ,(cadr tl) ,(caddr tl))))
	   );end mk-infappn


	   ;push exception name paired with its type onto exenv.
	   ;format exenv : (((exn.ty) .. (exn.ty)) ((exn.ty) ..))
	   (mk-exception
		(exceptionbindings
			(if (eq (caar tl) 'mk-and)
			   (cdar tl)
			   tl
			);end if
  		);end exceptionbindings
		unittyp;return unit
	   );end mk-exception

	   (mk-raise
		(let ((ex_typ (get_exntyp (car tl))));get type of exn.
		 (if (cdr tl);expression incl.!
		   (listtyping (cdr tl) `(,ex_typ) ty); check for same type
		   ty
		 );end if
		);end let
	   );end mk-raise

	   (mk-handle
	      (let ((ty_hdl; derive type for handler (= type of 1 rule)
			;check that all hrules have same type
			(listtyping
			   (cdr tl);hrules
			   (twistlist ty);tyvar list
			   ty; return ty (type of one rule)
		        );end listtyping
		     ));end
	        ;derive type for the whole handle exp.
		;(same as the type of exp and handler)
		;check that exp has same type as handler
		 (listtyping
		   `(,(car tl));expression
		    `(,ty_hdl)
		    ty_hdl; return type of handler.
		 );end listtyping
		);end let
	    );end mk-handle

	    (mk-withhand; type for handlerrule: exn with match.
		 ;if exn has type ty then match shuld have type ty->ty'	
		   (listtyping
			`(,(cons 'mk-fn (cdr tl)))
			 (list 
			    (list 'mk-funtyp (get_exntyp (car tl)) ty)
			  );end list
			  ty; return ty'
		  );end listtyping
	    );end mk-withhand

	   (mk-wildhand
	    (let ((ty (get_exntyp (car tl))));check that exn. is within scope
		(typing (cadr tl));typing expression
	    );end let
	   );end mk-wildhand

	   (mk-univhand
		(typing (car tl))
	   );end mk-univhand


	   (mk-case ; case exp of match -> (fn match) (exp)
		(typing `(mk-appn ,(cons `mk-fn (cdr tl)) ,(car tl)))
	   );end mk-case

	   (mk-while
		(listtyping (list (car tl)) (twistlist '(bool)) nil)
		(typing (cadr tl)) unittyp; return unittyp
	   );end mk-while  

	   (mk-andalso
		(typing `(mk-if ,(car tl) ,(cadr tl) (mk-boolconst false)))
	   );end mk-andalso

	   (mk-orelse
		(typing `(mk-if ,(car tl) (mk-boolconst true) ,(cadr tl)))
	   );end mk-orelse

	   (mk-if 
	   	(let ((ty (typing (cadr tl))))
		   (listtyping; check bool. exp.
			(list (car tl) (caddr tl))
			(list '(bool) ty) ty)
		);end let
	   );end mk-if

	   (mk-straint 
		(let ((ty (typing (cadr tl))))
		     (listtyping (list (car tl)) (list ty) ty)
		);end let
	   );end mk-straint

	   (mk-let ;type check in local environments
		(localtyping (car tl) (cadr tl))
	   );end mk-let 

	   (mk-local; typecheck in local environments
		(localtyping (car tl) (cadr tl))
	   );end mk-local


	   (mk-appn 
		;arguments for ref must be monotype 
	        ;but may be polytype in patterns!
		  (if (and (not structcheck) (eq (cadar tl) 'ref));
		 	(newl %monotypes (cons 'ref ty));checked in typech.
		  );end if

		  (ifn (eq (cadar tl) eq_sym);equality?
		    (listtyping tl (list (list `mk-funtyp ty ty$) ty) ty$)
		    (setq %eq_flg t);we only want to add to %coneq_l
			;from the lhs of the equality function(see mk-tuple)
		    (listtyping tl (list (list `mk-funtyp ty ty$) ty) ty$)
		  );end ifn	
	

		    ty$; return ty$
	   );end mk-appn
					     	

	   (mk-expseq
		(listtyping (car tl) (twistlist nil) (typing (cadr tl)))
	   );end mk-expseq

	   (mk-tuple
	     (let ((ty1
		   (cond (%eq_flg; argument to equality function!!
	;we only want to add elements to %coneq_l from lhs!
			(setq %eq_flg1 t)(setq %eq_flg nil)
		        (prog1
		  	   (typing (car tl));typing lhs of equality
			   (setq %eq_flg1 nil);reset %eq_flg1 
		        ));end prog1
		      (t (typing (car tl)))
		  )));end cond
	    	(cons 'mk-tupletyp
		  (cons ty1
		   (mapcar 'typing (cdr tl))
		  );end cons
		);end cons
	     );end let
	   );end mk-tuple

	   (mk-list
		(listtyping tl (twistlist ty) `(list ,ty))
	   );end mk-list

	   (mk-record
	     (let ((ty
		(find_missing_lab;find missing labels (if num. labels)
		   (sort_record
			(cons 'mk-recordtyp
			   (mapcar
			     '(lambda (x) (cons (car x) (typing (cdr x))))
			      tl;
			   );end mapcar
			);end cons
		   );end sort_record
		);end find_missing_lab
		   ));end ty
		(if (num_labp (caar tl))
		   (cons 'mk-tupletyp
			(mapcar 'cdr (cdr ty));filter out labels!
		   );end cons
		   ty
		);end if
	      );end let
	   );end mk-record

	   (mk-wildrecord	
	     (if structcheck
	      (let ((ty
		(fill_record
		   (sort_record
		      (cons 'mk-wildrecordtyp
			(mapcar
			   '(lambda (x) (cons (car x) (typing (cdr x))))
			    tl;
			);end mapcar
		       );end cons
		   );end sort_record
          	   t ;flag
		);end fill_record
	               ));end ty
		   (if (num_labp (caar tl));numeric labels
			(cons 'mk-wildtupletyp
			    (mapcar 'cdr (cdr ty))
			);end cons
			 ty
		    );end if
		);end let
	        (typech_failed '|record: wild record found in expression|)
	      );end if
	   );end mk-wildrecord

	   (mk-laypat
		(let ((ty1 (typing (cadr tl))))
		   (listtyping `(,(car tl)) `(,ty1) ty1)
		);end let
	   );end mk-laypat

	   (mk-fn 
	     (mapc;  check for mult. occ. of idents.
		'(lambda (x) (mult_occ (car x)))
		tl
	     );end mapc
	     (if (eq (length tl) 1); just one clause!
		(prog2
	  	     (varbindings (caar tl) mark)
			(popenv 
			 (list `mk-funtyp 
			   (structoff
				(typing
				   (structon (caar tl)); pattern
				);end typing
			     );end structoff
			    (typing (cdar tl)); expression
			 );end list
			);end popenv
		);end prog2

             ;else (several clauses)
	        (listtyping 
		   (mapcar `(lambda (funx)
			     `(mk-fn (,(car funx) . ,(cdr funx)))) tl 
	           );end mapcar
		   (twistlist ty)
		   ty
	        );end listtyping        
	      );end if
	   );end mk-fn

	   (mk-type
	     	(type_typing
		   (if (eq (caar tl) 'mk-and)
			(cdar tl)
			tl
		   );end if
	 	);end type_typing
		unittyp
	   );end mk-type

	   (mk-datatype
	      (datatype_typing
	  	(if (eq (caar tl) 'mk-and)
		  (cdar tl)
		  tl
		);end if
		'datatype; marker!
	       );end 
	       unittyp
	   );end mk-datatype
	
	   (mk-abstype
		(abstype_typing tl)
	   );end mk-abstype
		
	   ((mk-infixr mk-infix mk-nonfix)
		unittyp
	  );end infix

	   (mk-val
 	     (let ((%vartypes %vartypes))
		(typing (car tl)); val binding
	     );end let
	   );end mk-val

	   (mk-valbind
		(let ((ty (typing (cadr tl))));type of exp.
		   (mult_occ (car tl));test for mult. occ.
		   (prog2
		     (varbindings (car tl) 'mk-val)
		     (structoff
			(listtyping
			   (structon (list (car tl)));enable pat. checks!
			   (list ty) ty
			);end listtyping
		      );end structoff
		      (rplaca (car env) 'val)
		   );end prog1
		);end let
	     );end mk-valbind

	     (mk-rec
	 		(cond 
			   ((eq (caar tl) 'mk-and)
				(mapc
				   '(lambda (x)
					(ifn (eq (caaddr x)  'mk-fn)
					  (typech_failed
    '|val declaration: bad expression in recursive binding|)
					);end ifn
				     );end lambda
				     (cdar tl)
				);end mapc
				; pat=exp and pat=exp -> (pat,pat)=(exp,exp)
				(let ((x (split_and (cdar tl))) (l1)
					(l2))
				   (setq l1 (cons 'mk-tuple (car x)))
				   (setq l2 (cons 'mk-tuple (cdr x)))
				   (mult_occ l1);test for mult. occ.
			  ;extend environment before(!) typing expression:
				   (varbindings l1 'mk-val);
				   (valrec_typing `(,l1 ,l2))
				
				);end let
			     );end 
			     (t
				(ifn (eq (caaddar tl) 'mk-fn)
					  (typech_failed
   '|val declaration: bad expression in recursive binding|)
				);end ifn

				(mult_occ (cadar tl));check for mult. occ.
				(varbindings (car tl) 'mk-val);fun variable
				(valrec_typing (cdar tl))
			     );end t
			);end cond
	  );end mk-rec


           (mk-and
                (let
                   ((pattern
                        (cons `mk-tuple (mapcar `(lambda (x) (cadr x)) tl)))
                    (expr
                        (cons `mk-tuple (mapcar `(lambda (x) (caddr x)) tl))))
                   (typing
                      (cons `mk-valbind `(,pattern ,expr)))))

	   (mk-fun
	     (let ((%vartypes %vartypes));scope of tyvars
		(selectq (caar tl)
		   (mk-funbind
		       (typing; type check derived form!
			`(mk-val (mk-rec ,(adjust_clause (cdar tl))))
		      );end typing
		   );end mk-funbind
		   (mk-and
		     (typing
			`(mk-val (mk-rec ,(cons 'mk-and
			   (mapcar 
				'(lambda (x) (adjust_clause (cdr x)))
				 (cdar tl)
			    );end mapcar
			 )))
		     );end typing
		   );end mk-and
		);end selectq
	      );end let
	   );end mk-fun
	   
	   (mk-decseq
		(cons 'mk-decseqtyp (mapcar 'typing tl))
	   );end mk-decseq

; LCF Stuff
	  (MK=VARTYPE typety)
	  ((MK=VAR MK=CONST) termty)
	  ((mk-tyquot mk-quot MK=ANTIQUOT MK=TYPE=ANTIQUOT) (typing (car tl)))
	  (MK=TYPE  (listtyping (cdr tl) (twistlist typety) typety))
	  (MK=TYPED (listtyping tl (list termty typety) termty))
	  ((MK=COMB MK=PAIR MK=ABS MK=COND)
	   (listtyping tl (list termty termty termty ) termty))
	  (MK=NEG (listtyping tl (list formty) formty))
	  ((MK=CONJ MK=DISJ MK=IMP MK=IFF)
	   (listtyping tl (list formty formty) formty))
	  ((MK=FORALL MK=EXISTS) (listtyping tl (list termty formty) formty))
	  (MK=PREDICATE (listtyping (cdr tl) (list termty) formty))
	  ((MK=EQUIV MK=INEQUIV) (listtyping tl (list termty termty) formty))

	);end selectq
   );end let
);end typing
 
;***************************************************************************
;*        LISTTYPING
;***************************************************************************
;*
;*DESCRIPTION: unify types of objects in ob1 with the corresponding types in ty1
;*
;*LOCAL VARIABLES:  ob1 : list of ml objects.
;*		    ty1  : list of types.
;*		    ty   : type to be returned.
;*
;*COMMENTS: 
;*
;***************************************************************************
(de listtyping (ob1 ty1 ty)
    (let ((ok t))
	(while ob1
	   (let ((ty$ (typing (car ob1))));get type for first obj.
		(when (and (car ty1) (not (unifyt ty$ (car ty1))))
		   (incr type%errors)
		   (setq ok nil)
		   (llterpri)
		   (llprinc `|type error: |)
		   (print-ml-text (car ob1) %mlprintdepth)
		   (llterpri)
		   (let ((%temt tenv))
		        (ptoken |has an instance of type:|)
		        (pbreak 2 4)
			(printmty (tidy ty$) t)
		        (pnewline)
			(ptoken |which should match type:|)
			(pbreak 2 4)
			(printmty (tidy (car ty1)) t)
			(pnewline)
		    );end let
		);end when
	    );end let
	   (setq ob1 (cdr ob1))
	   (setq ty1 (cdr ty1))
	);end while
        (if ok ty (genmlink '%MLINK));generate implic. tyvar ifn ok so typech. can continue!
    );end let
);end listtyping

;***************************************************************************
;*	RECORD_DATATYPE
;***************************************************************************
;*
;*DESCRIPTION: Store information about defined types in the properties
;*	       of a unique symbol generated by uniquesym. The name of
;*	       the type constructor consed with the unique symbol is returned.
;*
;*LOCAL VARIABLES: tysym : unique symbol
;*
;***************************************************************************
(de record_datatype (ob mark)
    (let ((tysym (uniquesym 
	      (if (eq mark 'datatype) "datatype" "abstype")
	      (caddr ob))));
	(eval-remember
	   `(progn 
		(putprop ',tysym ,(length (cadr ob)) 'arity); no of tyvars
		(putprop ',tysym ',(cadr ob) 'tyvarl); list of tyvars
		(putprop ',tysym ',(caddr ob) 'tyname); type constructor
            );end progn
	);end eval..
        (cons (caddr ob) tysym)
    );end let
);end record_conctype

;*****************************************************************************
;*	RECORD_TYPE
;*****************************************************************************
;*
;*DESCRIPTION: Store information about type abbrevations in properties
;*	       of a unique symbol.
;*		arity : number of type variables
;*		abbrevtyp : type abbrevation
;*		tyname : type constructor
;*
;*****************************************************************************
(de record_type (l)
   (let ((tysym (uniquesym "type" (caddr l))))
	(eval-remember
	   `(progn
		(putprop ',tysym ,(length (cadr l)) 'arity)
		(putprop ',tysym ',(tidy (typing (cadddr l))) 'abbrevtyp)
		(putprop ',tysym ',(cadr l) 'tyvarl)
		(putprop ',tysym ',(caddr l) 'tyname)
	   );end progn
	 );end eval-rem
	 (cons (caddr l) tysym)
   );end let
);end record_type

;***************************************************************************
;*        DATATYPE_TYPING
;***************************************************************************
;*
;*DESCRIPTION: Process a datatype declaration.
;*
;***************************************************************************
(de datatype_typing (db_l mark);mark= 'datatype/abstype
   (let ((tyops (mapcar '(lambda (db) (record_datatype db mark)) db_l))
	 (constrs)(tycon_l)(tyvar_l) (noneq_l))
        (typebindings tyops)
	(mapc
	   '(lambda (db)
		(setq tyvar_l nil);reset tyvar_l for each binding!
		(let ((%vartypes
			(mapcar
			   '(lambda (v) 
			      (if (memq v tyvar_l);mult. occ. of tyvars ?
				(typech_failed
				   (concat
		'|datatype binding: multiple occurrence of type variable - |
			            v)
				);end typech_failed
				(newl tyvar_l v)
			      );end if
			      (cons v (genmlink v));generate explicit tyvar
			   );end lambda
			   (cadr db)
			)));end mapcar
		  (if (memq (cadr db) tyvar_l);mult. occ. of tyvars ?
			(typech_failed
			   (concat
	'|datatype binding: multiple occurrence of type variable - |
			    (cadr db))
			);end typech_failed
			(newl tyvar_l (cadr db))
		  );end if
		  (if (memq (caddr db) tycon_l);mult. occ. of tycons ?
			(typech_failed
			  (concat
	'|datatype binding: multiple occurrence of type constructor - |
			   (caddr db))
			);end typech_failed
			(newl tycon_l (caddr db))
		  );end if
		  (let ((ty1
			   (cons 
				(assoc1 (caddr db) tyops);uniq sym..
				 (mapcar 'cdr %vartypes))); (%mlink)
			    (constructors))
		    (mapc 
			'(lambda (con)
     			   (let ((ty0)) 
			     (let ((ty
				  (ifn (cddr con); no type
				     ty1
				     `(mk-funtyp 
				        ,(setq ty0 (typing (caddr con))) ,ty1)
				   )));end ifn
				;accumulate all constr. in this dec
				(newl constrs (cons (cadr con) ty))
				;accumulate constr. in this binding
				(newl constructors (cadr con))
		;if ty0<>nil then check if ty0 admits equality:
				(if ty0
				  (let ((eq_test 
				    (tycon_admits_eq ty0 
					(mapcar 'cdr tyops) ;list of uniq. syms.
					noneq_l)));end eq_test
				     (ifn eq_test;
				;ifn ty0 admits equality, neither does ty1!
				        (newl noneq_l (car ty1));so add ty1 to list
				;else build up a list of tycons occurring on rhs
				        (putprop
					  (car ty1)
					  (cons eq_test (get (car ty1) 'deplist))
				 	  'deplist
				         );end putprop
				      );end ifn
				   );end let
			        );end if
			     );end let
			   );end let
			);end lambda
			(reverse (cdddr db))
		      );end mapc
			;give unique symbol constructors property:
		   (eval-remember
		      `(putprop 
			',(assoc1 (caddr db) tyops) ',constructors 'constructors
		      );end putprop
		    );end eval..
		   );end let
		);end let
	   );end lambda
	   db_l
	);end mapc
	(newl env (cons 'constructors constrs))
        ;give each tycon a equality property !
	(mapc
	   '(lambda (x) 
	      (eval-remember
	        `(putprop ',(cdr x) 
		   ,(ifn (memq (cdr x) noneq_l) ;tycon admits eq itself!
			   ;check if all tycons on rhs also admits eq:
			(if (ok_dep noneq_l (get (cdr x) 'deplist)) t)
		   );end ifn
		     'equality
	           );end putprop 
		);end eval...
	      );end lambda
	    tyops
	);end  mapc
   );end let
);end datatype_typing	

;*****************************************************************************
;*	ABSTYPE_TYPING
;*****************************************************************************
;*
;*DESCRIPTION: Process an abstract type declaration. The scope of the
;*	       constructors declared in the datatype binding is the with
;*	       part of the abstype declaration.
;*
;*****************************************************************************
(de abstype_typing (l)
   (let ((save_env0 env) (save_env1) (save_tenv1) (ty))
  	(datatype_typing ;datatype binding!
	   (if (eq (caar l) 'mk-and)
		(cdar l) `(,(car l))
	   );end if
	   'abstype; marker
	);end datatype_typing
	(setq save_env1 env);we want to hide constructors !
	(setq save_tenv1 tenv)
	(setq ty (typing (cadr l)));typing decl.
	(setq env (splice env save_env0 save_env1));clean up environments
	ty
   );end let
);end abstype_typing

;*****************************************************************************
;*	TYPE_TYPING
;*****************************************************************************
;*
;*DESCRIPTION: Process a type declaration.
;*
;*****************************************************************************
(de type_typing (tb_l)
   (let ((tyops (mapcar 'record_type tb_l))(tycon_l)(tyvar_l))
	(mapcar ; check for mult. occ. of tycons
	   '(lambda (x) (if (memq (caddr x) tycon_l)
		(typech_failed 
			(concat 
		'|type declaration: multiple occurrence of type constructor - |
		    (caddr x)))
		(newl tycon_l (caddr x)))
		(setq tyvar_l nil);reset tyvar_l for each binding
		(mapcar
		   '(lambda (y)
			(if (memq y tyvar_l);mult occ. of tyvar
			  (typech_failed 
				(concat
	'|type declaration: multiple occurrence of type variable - |
				  y))
			  (newl tyvar_l y)
			);end if
		     );end lambda
		     (cadr x)
		);end mapcar
	     );end lambda
	     tb_l;
	);end mapcar
	(typebindings tyops); add layer to tenv.
   );end let
);end type_typing

;*****************************************************************************
;*	VALREC_TYPING
;*****************************************************************************
;*
;*DESCRIPTION: Type check recursive val binding.
;*
;*****************************************************************************
(de valrec_typing (l)
   (let ((ty1 (structoff (typing (structon (car l))))));typing pattern
	(listtyping (cdr l) (list ty1) ty1)
	(rplaca (car env) 'val)
	ty1
   );end let
);end valrec_typing   

;*****************************************************************************
;*	LOCALTYPING
;*****************************************************************************
;*
;*DESCRIPTION: Type check local declaration. Pointers to the environments are
;*	       saved before and after type checking the first dec. 
;*	       This is to make the first dec. local to the second.o
;*
;*****************************************************************************
(de localtyping (dec1 dec_or_exp)
   (let ((save_env0 env) (save_tenv0 tenv)
	 (save_ex0 exenv) (save_env1) (save_tenv1) (save_ex1) (ty))
	(typing dec1)
	(setq save_env1 env)
	(setq save_tenv1 tenv)
	(setq save_ex1 exenv)
	(setq ty (typing dec_or_exp))
	;remove bindings from dec1 :
	(setq env (splice env save_env0 save_env1)); 
	(setq tenv (splice tenv save_tenv0 save_tenv1)); 
	(setq exenv (splice exenv save_ex0 save_ex1)); 
	ty;return ty!
   );end let
);end localtyping

;***************************************************************************
;*        VARBINDINGS
;***************************************************************************
;*
;*DESCRIPTION: Push a new layer onto the environment env.
;*
;*CALLING: layer.
;*
;***************************************************************************
(de varbindings (st binder)
	(newl env (cons binder (layer st)))
);end varbindings

;***************************************************************************
;*        LAYER
;***************************************************************************
(de layer (st)
	(selectq (car st)
	   (mk-valbind (layer (cadr st)))
	   (mk-rec (layer (cadr st)))
	   (mk-and (layer1 (cdr st)))
	   ((mk-var mk-opvar)
		     `(,(cons (cadr st) (genmlink '%MLINK)))
	   );end mk-var
          
	   ((mk-const mk-opconst mk-con mk-opcon) nil); 


           ((mk-tuple mk-list)
		(layer1 (cdr st)); (cdr st)=cont. of tuple or list
	   );end mk-tuple

	   ((mk-record mk-wildrecord)
		(layer1
		   (mapcar 
			'(lambda (x) (cdr x))
			 (cdr st)
		   );end mapcar
		);end layer1
	   );end mk-record

	   ((mk-appn mk-infappn)
		   (layer1 (cddr st))
	   );end mk_appn

	   (mk-straint
		(layer (cadr st))
	   );end mk-straint

	   (mk-laypat
		(layer1 (cdr st))
	   );end mk-laypat

	   (t nil)
	);end selectq
);end layer

(de layer1 (stl)
	(if stl
	   (append (layer (car stl)) (layer1 (cdr stl)))
	);end if
);end layer1

;*****************************************************************************
;*	EXCEPTIONBINDINGS
;*****************************************************************************
;*
;*DESCRIPTION: Add a new layer to the exception environment exeenv.
;*	       format: (.. ((exn . ty) ..) .. )
;*			exception exn1 :ty = exn2
;*
;*****************************************************************************
(de exceptionbindings (l)
   (let ((eb_l))
   	(mapc
	   '(lambda (x)
		(if (and (cddr x) (not (atom (cadr x))); expl. ty + exn2
		   (not (unifyt 
			(typing (get_exntyp (caddr x)))
			(typing (cdadr x)))))
		     (typech_failed; different types!
			(concat 
	         '|exception declaration: exception name of wrong type - | 
			  (caddr x)))
		);end if
		(newl eb_l
		   (cons 
; exceptions get type unit by default!
;		 	   (if (atom (cadr x)); expl. type ?
;			        (cadr x)
			        (caadr x)
;			   );end if
		   (cond
			((not (atom (cadr x))) (tidy (typing (cdadr x))))
		   	((cddr x) (tidy (get_exntyp (caddr x))));ty of exn2
			(t ;generate tyvar! 
			  `(,(concat prime_sym (uniquesym "exn" (gensym)))))_
		   );end cond
		  );end cons
		);end newl
	    );end lambda
	    l
	);end mapc
	(newl exenv eb_l); add new layer to exenv
   );end let
);end exceptionbindings

;***************************************************************************
;*        ADJUST_CLAUSE
;***************************************************************************
;*
;*DESCRIPTION: Transform the derived form:
;*			var apat11 .. apat1n = exp1 |
;*			var apatm1 .. apatmn = expm     into the equiv. form:
;*
;*			var = fn x1 => .. fn xn =>
;*			   case (x1, .. ,xn) of
;*			     (apat11 .. apatan) => exp1
;*				     ..
;*			     (apatm1 .. apatmn) => expn
;*
;*LOCAL VARIABLES: fun_nam : function name
;*		   no_of_apat : number of atomic patterns.
;*
;***************************************************************************
(de adjust_clause (l)
	(let ((fun_name (cadar l)) (no_of_apat (length (caddar l)))
		  (var_l) (n))
	   (setq n no_of_apat)
	   (while (> n 0); generate dummy variables!
		(newr var_l `(mk-var ,(uniquesym "tempvar" fun_name)))
		(setq n (sub1 n))
	   );end while
	   `(mk-valbind (mk-var ,fun_name) 
		,(gen_fun l no_of_apat var_l fun_name))
	);end let
);end adjust_clause

;***************************************************************************
;*      GEN_FUN  
;***************************************************************************
;*
;*DESCRIPTION: Builds up a list of expressions and a list of atomic patterns.
;*	       A check is made that all cluses have the same number of
;*	       atomic patterns and that they all use the same function name.
;*
;*LOCAL VARIABLES: exp_l : list of expressions.
;*		   apat_l : list atomic patterns.
;*
;***************************************************************************
(de gen_fun (l n var_l fun_name)
   (let ((exp_l) (apat_l)) 
   	(while l
	   (ifn (eq (length (caddar l)) n)
		(typech_failed 
		 (concat
		   '|fun declaration: expected | n  '| atomic | 
			(if (eq n 1) '|pattern| '|patterns|)
		    '| in declaration of | fun_name '| but found |
			(length (caddar l)))
		);end typech_failed
	   );end ifn
	   (ifn (eq (cadar l) fun_name)
		(typech_failed
		  (concat
			'|fun declaration: expected function name | fun_name
			'| but found | (cadar l)) 
		);end typech_failed
	   );end ifn
	   (newr apat_l
		(if (eq n 1)
		   (caaddar l)
		   (cons 'mk-tuple (caddar l))
		);end if
	   );end newr
	   (newr exp_l
		(if (caddddar l);type constr.
		   `(mk-straint ,(cadddar l) ,(caddddar l))
		   (cadddar l)
		);end if
	   );end newr
	   (setq l (cdr l))
	);end while
	   (gen_fun1 var_l exp_l apat_l var_l)
    );end let
);end gen_fun


;***************************************************************************
;*        GEN_FUN1
;***************************************************************************
;*
;*DESCRIPTION: Returns: (mk-fn (mk-var . ) .. (mk-case ... ))
;*
;***************************************************************************
(de gen_fun1 (l exp_l apat_l var_l)
   (prog ()
      (cond
	   ((null l); generate case tree
	       (return
	          (gen_case apat_l exp_l var_l)))
	   (t
		(return
	          `(mk-fn (,(car l) .
	            ,(gen_fun1   
		        (cdr l) exp_l apat_l var_l))))
		);end return
	);end cond
   );end prog
);end gen_fun

;***************************************************************************
;*        GEN_CASE
;***************************************************************************
;*
;*DESCRIPTION: Generate a parse tree for the case expression.
;*
;***************************************************************************
(de gen_case (ap_l ex_l var_l)
     (prog (res)
        (setq res 
	   `(mk-case ,(if (eq (length var_l) 1)
	      (car var_l)
	      (cons `mk-tuple var_l)
	      ));end mk-case
        );end setq
	(while ap_l 
	   (newr res `(,(car ap_l) . ,(car ex_l)))
	   (setq ap_l (cdr ap_l))
	   (setq ex_l (cdr ex_l))
	);end while
	(return res)
     );end prog
);end gen_case

;***************************************************************************
;*        GET_TYPE
;***************************************************************************
;*
;*DESCRIPTION: Get the type of a type variable or constructor. 
;*
;*	mark is passed to gettypeid to cope with the following:
;*		datatype foo=a|b|c;
;*		datatype foo=a|b;
;*		c;  (*should now be unbound, but still has constr. prop.*)
;*		    (*hence two prop. one for var and another for con*)
;*
;***************************************************************************
(de getid_typ (%id mark)
    (cond  ((gettypeid env mark))
	   (t (incr type%errors)
	      (llterpri)
	      (llprinc `|unbound or unassignable variable: |)
	      (llprinc %id)	
	      (llterpri)
	      (varbindings (list 'mk-var %id) 'mk-letref)
	      (genmlink '%MLINK)))
); gettype

;***************************************************************************
;*        GET_BUILTIN
;***************************************************************************
;*
;*DESCRIPTION: Get built-in type.
;*
;***************************************************************************
(de get_builtin (mark)
    (when (and (eq %id lastvalname) (assq 'mk-fn env))
      (llprinc '|may not use '|)
      (llprinc lastvalname)
      (llprinc '| in a function body|)
      (llterpri)
      (*exit typecheck nil))
    (if (eq mark 'var)
       (get %id 'mlvartype)
       (get %id 'mlcontype)
    );end if
); get_builtin

;***************************************************************************
;*        GETTYPETID
;***************************************************************************
;*
;*DESCRIPTION: Get type of %id in environment e or if e=nil get type
;*	       from %id`s mlcontype  or mlvartype property.
;*
;***************************************************************************
(de gettypeid (e mark)
    (ifn e

	  (mutant (get_builtin mark) nil)	
	;else
	 (let ((ty 
		   ;%id could be
		   (if (or 
			(and (eq mark 'con) (eq (caar e) 'constructors))
			(and (eq mark 'var) (memq (caar e) '(val mk-val)))
			(and (eq mark 'var) (eq (caar e) 'mk-fn));abstr
			);end or
			   (assoc1 %id (cdar e))))
		   );end ty
	   (cond 
	       ((null ty)
		  (gettypeid (cdr e) mark))
		 ((memq (caar e) '(val abs)) (mutant ty (cdr e)))
		 (t ty)
           );end cond
         );end let
     );end if
);end gettypeid

;***************************************************************************
;*        GETTYPET
;***************************************************************************
;*
;*DESCRIPTION: Get internal representation for type of type constructor.
;*
;*CALLED BY: typing.
;*
;***************************************************************************
(de gettypet (tyid)
    (prog (ty)
	   (cond
		((setq ty (gettypetid tyid tenv))
			(return ty))
		((typech_failed (concat
		  '|type constructor: | tyid '| is out of scope|)))
	   );end cond
      );end prog
);end gettypet

;***************************************************************************
;*        GETTYPETID
;***************************************************************************
;*
;*DESCRIPTION: Get type of tyid in either %deftypes (global) or in tenv.
;*
;***************************************************************************
(de gettypetid (tyid te)
	   (cond
		((null te) (assq1 tyid %deftypes))
		((assq1 tyid (car te)))
		((gettypetid tyid (cdr te)))
	   );end cond
);end gettypetid


;***************************************************************************
;*        CHECKTYPE
;***************************************************************************
;*
;*DESCRIPTION: Checks two things:
;*	          1) if the type constructor has been declared in an
;*		     abstype dec or in a datatype dec then a check
;*		     is made that the number of type variables used in the
;:		     declaration corresponds to the number of type arguments
;*		     in idarg and true is returned.	
;*
;*		   2) if the type constructor was declared in a type dec
;*		      using type variables, then a similar check as described above is
;*		      made for the number of type arguments in idargs and nil
;*		      is returned..
;*
;***************************************************************************
(de checktype (idargs)
   (let ((ty (gettypet (car idargs))))
	(cond
	   ((atom ty); abstype or generative type!
		(cond
		   ((not (eq (get ty `arity) (length (cdr idargs))))
		      (typech_failed
			(concat
			   '|type expression: type constructor | (car idargs) '| expects |
			   (get ty 'arity)  
			    (if (> (get ty 'arity) 1) '| arguments| '| argument|)
		   	    '|, but was given |
			   (length (cdr idargs))
			)));end typech_failed	
		   (t t)
                );end cond
	     );end atom
	   (t ;type abbrevation with type variables!
	     (cond
		((not (eq (get (car idargs) `arity);no of args should
					           ;match no of tyvars
			  (length (cadr idargs))))
		      (typech_failed
			(concat
			   '|type expression: type constructor | (car idargs) '| expects |
			   (get ty 'arity)  
			    (if (> (get ty 'arity) 1) '| arguments| '| argument|)
		   	    '|, but was given |
			   (length (cdr idargs))
			)));end typech_failed	
	        (t nil);return nil (not an abstype)
	      ));end cond
        );end cond
    );end let
);end checktype

 
;*****************************************************************************
;*	GET_EXNTYP
;*****************************************************************************
;*
;*DESCRIPTION: Get type of exception name.
;*
;*****************************************************************************
(de get_exntyp (exn)
   (mutant
     (or
	(get_exntyp1 exn exenv);exn decl. in this dec?
	(get exn 'extyp);prev. declared !
	(typech_failed
	   (concat '|exception name: | exn '| is out of scope|)
	);end typech_failed
      );end or
      nil;
   );end mutant
);end get_exntyp

(de get_exntyp1 (exn x_env)
   (cond
	((null x_env)  nil)
	((assoc1 exn (car x_env)))
	(t (get_exntyp1 exn (cdr x_env)))
    );end cond
);end get_exntyp1

;***************************************************************************
;*        MLINK
;***************************************************************************
;*
;*DESCRIPTION: true if ty is implicit (ie (%MLINK)) or explicit (|'tyvar|)
;*	       type variable
;*
;*COMMENTS: Note that the type variable may have been unified with some type.
;*
;***************************************************************************
(de mlink (ty) 
	(ifn (atom ty) 
	   (or
		(eq (car ty) '%MLINK);implicit !!
		(is_type_var (car ty)); explicit !!
	    );end or
	);end ifn
);end mlink

;***************************************************************************
;*        INSTOF
;***************************************************************************
;*
;*DESCRIPTION: Check if ty has been unified with some type.
;*
;*COMMENTS: Returns the type ty has been unified with.
;*
;***************************************************************************
(de instof (ty) 
	(if (mlink ty) 
	   (if (is_type_var (car ty));explicit tyvar
		  nil	;cannot be instan. by concrete type but by implicit
			;tyvar, hence return nil not to lose info
			;about it being explicit (in prune).
		   (cdr ty); else implicit type, return instance.
	    );end if
	);end if
);end instof

;***************************************************************************
;*        PRUNE
;***************************************************************************
;*
;*DESCRIPTION: If ty has been unified with ty1 then ty1 is returned else
;*	       ty is returned.
;*
;*COMMENTS: prune gets the type ty1 by cdr`ing down ty by calling instof.
;*
;***************************************************************************
(de prune (ty) (if (instof ty) (prune (instof ty)) ty))	;prune

(de prune1 (ty) (if (cdr ty) (prune (cdr ty)) ty));prune for explicit tyvars!

;***************************************************************************
;*        OCCURST
;***************************************************************************
;*
;*DESCRIPTION: Checks if v occurs in ty.
;*
;***************************************************************************
(de occurst (v ty) 
   (occursbt v (prune ty))
);occurst

;***************************************************************************
;*        OCCURSBT
;***************************************************************************
(de occursbt (tyv bty)
   (if (memq (car tyv) '(mk-recordtyp mk-wildrecordtyp))
	(setq tyv (cons (car tyv)
	   (mapcar '(lambda (x) (cdr x)) (cdr tyv)))));ignore labels
   (if (memq (car bty) '(mk-recordtyp mk-wildrecordtyp))
	(setq bty (cons (car bty)
	   (mapcar '(lambda (x) (cdr x)) (cdr bty)))))
    (if (mlink bty)
	(eq tyv bty)
	(exists '(lambda (ty) (occurst tyv ty))  (cdr bty)))
);end occurstb

;***************************************************************************
;*        POLY
;***************************************************************************
;*
;*DESCRIPTION: Checks if type is polymorphic.
;*
;***************************************************************************
(de poly (ty) (polyb (prune ty)))		;poly

;***************************************************************************
;*        POLYBT
;***************************************************************************
(de polyb (bty)
    (or 
	(mlink bty) (exists 'poly 
		(if (memq (car bty) '(mk-recordtyp mk-wildrecordtyp))
		    (mapcar 'cdr (cdr bty))
		    (cdr bty)))
     );end or
);polyb


;***************************************************************************
;*        UNIFYT
;***************************************************************************
;*
;*DESCRIPTION: Returns true if types can be unified.
;*
;***************************************************************************
(de unifyt (ty1 ty2) (unifybt (prune ty1) (prune ty2)))	;unifyt

;*****************************************************************************
;*	UNIFY_RECORD
;*****************************************************************************
;*
;*DESCRIPTION: Unifies records and wildrecords.
;*
;*****************************************************************************
(de unify_record (bty1 bty2)
   (if (num_labp (caadr bty1));num label in bty1
	(if (num_labp (caadr bty2));and in bty2
	   (unify_record1 bty1 bty2)
	);end if
	(ifn (num_labp (caadr bty2))
	   (unify_record1 bty1 bty2)
	);end ifn
   );end if
);end unify_record

;*******************************************************************************
;*	UNIFY_RECORD1
;*******************************************************************************
(de unify_record1 (bty1 bty2)
   (prog (l1 l2 l temp lay)
 	(setq l1 (cdr bty1))(setq l2 (cdr bty2))
	(if (and (eq (car bty1) 'mk-recordtyp)
		 (eq (car bty2) 'mk-recordtyp)
		 (neq (length l1) (length l2)))
	   (return nil)
	);end if
	(while l1; iterate on l1
	   (setq lay (assoc (caar l1) l2));pick first label-item pair
	   (cond
		(lay ;label exists in bty2!
		   (ifn (unifyt (cdar l1) (cdr lay));cann the types be unified?
			(return nil)
		   );end if
		   (setq l2 (remove_lay (car lay) l2)));yes, remove the pair!
		(t 
		    (if (eq (car bty2) 'mk-wildrecordtyp);missing in bty2!
			(setq l (cons (car l1)  l));build up a list of missing pairs!
			(setq temp t);error! (cannot return from while!)
		    ));end if
	   );end cond
	   (setq l1 (cdr l1))
	);end while
	(if temp (return nil))
	(cond
	   ((and (eq (car bty1) 'mk-wildrecordtyp)
		 (eq (car bty2) 'mk-wildrecordtyp))
		(ifn (null l) 
		   (rplacd bty2 (append (cdr bty2) l)));union!
		(ifn (null l2)
		   (rplacd bty1 (append (cdr bty1) l2)));union!
		(return t))
	   ((eq (car bty1) 'mk-wildrecordtyp);bty2 is of record type!
		(ifn (null l) (return nil));each pair in 1 exists in 2?
		(ifn (null l2)
		   (rplacd bty1 (append (cdr bty1) l2)));union!
		   (rplaca bty1 'mk-recordtyp);mk-wildrecord becomes mk-record!
		   (return t))
	   (t (ifn (null l2) ;both record types!
		(return nil)
		(return t)))
	 );end cond
   );end prog
);end unify_record1


;***************************************************************************
;*	UNIFYBT
;**************************************************************************** 
;unify bty1 with bty2
(de unifybt (bty1 bty2)
    (cond
      ((eq bty1 bty2))
      ((mlink bty1) (unify_var bty1 bty2))
      ((mlink bty2) (unify_var bty2 bty1))
      ((eq (car bty1) 'mk-recordtyp)
		(if (memq (car bty2) '(mk-recordtyp mk-wildrecordtyp))
		   (unify_record bty2 bty1)))
      ((eq (car bty1) 'mk-wildrecordtyp) 
		(if (memq (car bty2) '(mk-recordtyp mk-wildrecordtyp))
		   (unify_record bty1 bty2)))
      ((memq (car bty1) '(mk-wildtupletyp mk-tupletyp))
       (unify_tuple bty1 bty2))
      ((memq (car bty2) '(mk-wildtupletyp mk-tupletyp))
       (unify_tuple bty2 bty1))
      ((eq (car bty2) 'mk-wildrecordtyp)
		(if (memq (car bty2) '(mk-recordtyp mk-wildrecordtyp))
		   (unify_record bty1 bty2)))
      ((eq (car bty1) (car bty2))
       (unifytl (cdr bty1) (cdr bty2)))
   );end cond
);unifybt

; unify type variable (tyv) with bty
; copied from Hedlund's in-line code
(defun unify_var (tyv bty)
    (cond ((is_type_var (car tyv));tyv explicit tyvar!
	   (if (and (mlink  bty);bty is 
		    (not (is_type_var (car bty)));implicit, ok!
	       );end and
	       (ifn (occursbt tyv bty)
		    (rplacd bty tyv);;inst. implic. tyvar!
	       );end ifn			
	       (if (equal tyv bty);could be the same explicit
		   t	;type variable in which case we return t
		   (typech_failed ;else fail !
		       (concat '|type variable: | (car tyv)
			       '| cannot be constrained within its scope|
		       ));end typech_failed
	       );end if
	   ));end if 
	  ((occursbt tyv bty) nil)
	  (t (rplacd tyv bty)))) ; unify_var

; unify tuples
; copied from Hedlund's in-line code
(defun unify_tuple (bty1 bty2)
    (and (memq (car bty2) '(mk-wildtupletyp mk-tupletyp))
	 (prog ()
	       (let ((l) (l1 (cdr bty1)) (l2 (cdr bty2)))
		    (while l1; iterate on l1
			   (if l2 
			       (ifn (unifyt (car l1) (car l2))
				    (return nil))
			       (newl l (car l1));build up list of missing comp.
			   );end if
			   (setq l1 (cdr l1))
			   (setq l2 (cdr l2))
		    );end while
		    (if l2;still components in l2
			(if (eq (car bty1) 'mk-wildtupletyp);ok if wild!
			    (rplacd bty1 (append (cdr bty1) l2));union
			    (return nil);ifn wild: error!
			);end if
		    );end if
		    (cond  
			   ((eq (car bty2) 'mk-wildtupletyp);two wilds!
			    (if l (rplacd bty2 l)));union
			   (t (if l;surlus of components in l1!
				  (return nil);error !
				  (rplaca bty1 'mk-tupletyp);no longer wild!
			      ));end if
		    );end cond
		    (return t))))); unify_tuple

;***************************************************************************
;*        UNIFYTL
;***************************************************************************
;*
;*DESCRIPTION: Unify corresponding types in both lists. 
;*
;***************************************************************************
(defun unifytl (tyl1 tyl2)
 (cond
  ((null tyl1))
  ((unifyt (car tyl1) (car tyl2)) (unifytl (cdr tyl1) (cdr tyl2)))
))  ;unifytl

;***************************************************************************
;*        MUTANT
;***************************************************************************
;*
;*DESCRIPTION: Rename type variables occuring in ty.
;*
;***************************************************************************
(de mutant (ty %env) 
    (if (poly ty) (let ((%l nil)) (mutant1 ty)) ty)
);mutant

;***************************************************************************
;*        MUTANT1
;*
;***************************************************************************
(de mutant1 (ty)
    (cond
      ((memq (car ty) '(mk-recordtyp mk-wildrecordtyp))
	   (cons (car ty)
	      (mapcar
		'(lambda (x) (cons (car x) (mutant1 (cdr x))))
		 (cdr ty)
	      );end mapcar
	   ));end cons		
      ((instof ty) (mutant1 (instof ty)) )
      ((mlink ty);explicit or implicit tyvar
       (cond ((assq1 ty %l));already renamed!
	     ((and (is_type_var (car ty)) (assoc1 ty %l)));must use assoc for
	     ((immut ty %env) ty)			  ;explicit tyvars!
	     (t (let ((mlink (genmlink '%MLINK)))
		(if (is_type_var (car ty));explicit type variable!
		;add explit/implict tyvar pair on %generic to enable
		;top level loop to print the explicit tyvar if
		;it is not instantiated.
		;should several variables have the same explicit type variable
		;then the first occuring variable keeps it's explicit
		;type variable, the others get new type variables in tidy, before
		;getting printed at top level
		;(eg the tuple (op ::,op ::) where :: has type 'a -> 'a list,
		;would be printed as ('a -> 'a list)  ('b -> 'b list) )
		   (ifn (revassoc ty %generic) ;only one occurrence permited
			(newl %generic (cons mlink ty)))
	         );end if
		 (cdar (newl %l (cons ty mlink)))))
	));end cond
      ((cons (car ty) (mapcar 'mutant1 (cdr ty))))
    );end cond
);end mutant1


;***************************************************************************
;*        IMMUT
;***************************************************************************
;*
;*DESCRIPTION: Checks if a type variable is immutable.
;*
;*COMMENTS: An explicit type variable can not be renamed (ie made generic)
;*	    if it is an explicit tyvar in a type constraint (ie exists in %vartypes)
;*
;***************************************************************************
(de immut (tyv e)
    (and e
	 (or (and (not (memq (caar e) '(val abs)))
		  (exists '(lambda (x) (occurst tyv (cdr x))) (cdar e)))
	     (revassq tyv %vartypes);cannot be renamed within its scope
	      (immut tyv (cdr e))))
);immut


;***************************************************************************
;*        TYPEINIT
;***************************************************************************
(de typeinit ()
	(setq unittyp `(mk-recordtyp))
	(setq booltyp `(mk-consttyp bool))
	(setq inttyp `(mk-consttyp int))
	(setq realtyp `(mk-consttyp real))
	(setq stringtyp `(mk-consttyp string))
	(setq %emt nil)
	(setq %exemt nil)
	(setq %temt nil)

; LCF stuff
        (setq objty '(obj))
        (setq typety '(type))
        (setq termty '(term))
        (setq formty '(form))
        (setq thmty '(thm))
);end type_init 

;***************************************************************************
;*        TYPE_CHECK
;***************************************************************************
;*
;*DESCRIPTION: Type check top level construction.
;*
;*
;*LOCAL VARIABLES: env : environment,  pairs of id`s and types during 
;*			  type checking. Initially set to %emt.
;*		   tenv : environment,  ml defined types and abstract
;*			  types during type checking. Initially set to %temt.
;*	           exenv : exception names and thier associated types.
;*
;***************************************************************************
(de typecheck (ob)
	(let ((ph (car ob)) (tenv %temt) (env %emt) (type%errors 0) 
	      (asscheck) (structcheck) (%monotypes) (%vartypes) (exenv %exemt)
	       (%eqtypes) (%overload))

	   (let ((ty (tidy (typing ob))))
		(unless (zerop type%errors)
		  (llprinc type%errors)
		  (llprinc '| error|)
		  (if (> type%errors 1) (llprinc '|s|))
		  (llprinc '| in typing|)
		  (llterpri)
		  (*exit typecheck nil))

		;check overloaded functions
		(mapc
		   '(lambda (x)
			(cond
			  ((memq (car x) num_ops)
			     (ifn (memq (car (tidy (cdr x))) '(int real))
				(typech_failed
				  (concat
'|overloaded function: unable to resolve type of argument for | (car x)))
			   ));end ifn
			 ((memq (car x) nums_ops)
			    (ifn (memq (car (tidy (cdr x))) '(real int string))
			      (typech_failed
				(concat
'|overloaded function: unable to resolve type of argument for | (car x))
			     )));end ifn
			  ));end cond end lambda
			%overload
		);end mapc
		;check types of argumnts to the equality function
		(mapc
		   '(lambda  (x)
			(cond ((not (admit_equality  (tidy (car x))))
				;two possibilities for error:
			 (if (mlink (tidy (car x)));unresolved type!
			   (typech_failed (concat
        '|overloaded function: unable to resolve type for op | (cdr x)))
			   (ptoken |overloaded function: equality not admited for type |)
			   (pbreak 2 4)
			   (printmty (tidy (car x)) t)
			   (pnewline)
			   (*exit typecheck nil)	
			 ));end if
			);end cond
		    );end lambda
		    %eqtypes
		);end mapc
		;check that types in %monotypes are monotypes.
		(mapc 
		   '(lambda (x) 
			(if (poly (cdr x))
			   (typech_failed 
	   (if (memq (car x) '(print makestring)); 
      (concat '|function application: cannot resolve type of argument to | (car x))
      (concat '|function application: argument to | (car x) '| is not monotype|)
	   );end if
			   );end typech_failed
			);end if
		     );end lambda
		     %monotypes
		);end mapc
		;check types of all new exceptions declared at top level
		;must be monotype
		(mapc
		   '(lambda (x)
			(mapc
			   '(lambda (y)
				(if (poly (cdr y))
				   (typech_failed 
			(concat '|exception declaration: | (car y)
		'| must be constrained with a monotype at top level|))
				);end if

			   );end lambda 
			   x
			);end mapc
		     );end lambda
		     exenv
		);end mapc
		(while (neq tenv %temt)
		   (newr %thistydec (car tenv))
		   (setq tenv (cdr tenv))
		);end while
		(while (neq exenv %exemt)
			(newr %thisexdec (car exenv))
			(setq exenv (cdr exenv))
		);end while
		(while (neq env %emt)
			(tidycdrs (cdar (newr %thisdec (car env))))
			(setq env (cdr env))
		);end while
	        ty
	   );end let
	);end let
);end tycheck

;***************************************************************************
;*        UPDATETYPES
;***************************************************************************
;*
;*DESCRIPTION: update %deftypes and give variables, exception names and constructors 
;*	       their type properties.
;*
;***************************************************************************
(de updatetypes ()
  (let ((l %thisdec) (k %thistydec) (j %thisexdec))
    (cond
      (%sections
        (if %thisdec (newl %emt %thisdec))
        (if %thistydec (newl %temt %thistydec)))
      (t 
	;update exception names
	(while j
	   (putpropl (car j) 'extyp)
	   (setq j (cdr j))
	);end while
	(while k
	  (setq %deftypes (append (car k) %deftypes))
	  (setq k (cdr k))
	);end while
        (while l
	    (putpropl (cdar l) 
		(if (eq (caar l) 'constructors)
		   'mlcontype
		   'mlvartype
		);end if
	    );end putpropl
	    (setq l (cdr l))
        );end while
      );end t
    );end cond
  );end let
);end updatety.

(de putpropl (l prop)
    (mapcar '(lambda (x) (putprop (car x) (cdr x) prop)) l))	;putpropl


