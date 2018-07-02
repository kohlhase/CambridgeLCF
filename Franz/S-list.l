;******************************************************************************
;*
;*	S-list
;*
;******************************************************************************
; functions operating on lists.
; Origin: EDINBURGH LCF (Milner,Gordon,Wadsworth...) 
; Modified: CAMBRIDGE LCF (Huet,Paulson,Cousineau...) 

(eval-when (compile)
  (include S-constants)
  (include llmac)
  (include S-macro)
  (genprefix lis))



(dml |paired_mem| 2 member (mk-funtyp (mk-tupletyp (|'a|) (list (|'a|))) (bool)))

(dml |flat| 1 ml-flat (mk-funtyp (list (list (|'a|))) (list (|'a|))))
(de ml-flat (ll)
    (apply (function append) ll)
);ml-flat

(dml |paired_map| 2 ml-map  
	(mk-funtyp (mk-tupletyp (mk-funtyp (|'a|) (|'b|)) (list (|'a|))) (list (|'b|))))
(de ml-map  (%%f l)
    (mapcar '(lambda (x) (ap %%f x)) l))	;ml-map

(dml |paired_exists| 2 ml-exists  
   (mk-funtyp (mk-tupletyp (mk-funtyp (|'a|) (bool)) (list (|'a|))) (bool)))
(de ml-exists  (p l)
    (tag found (while l (if (ap p (nextl l)) (*exit found t))) nil))	;ml-exists

(dml |paired_forall| 2 ml-forall  
   (mk-funtyp (mk-tupletyp (mk-funtyp (|'a|) (bool)) (list (|'a|))) (bool)))
(de ml-forall  (p l)
    (tag found (while l (ifn (ap p (nextl l)) (*exit found nil))) t))	
;ml-forall


(dml |paired_rev_itlist| 3 ml-rev_itlist
    (mk-funtyp 
	(mk-tupletyp 
	   (mk-funtyp (|'a|) (mk-funtyp (|'b|) (|'b|)))
	   (list (|'a|))
	   (|'b|)
	) 
    (|'b|)))

(de ml-rev_itlist  (f l x)
    (while l (setq x (ap (ap f (nextl l)) x))) x)	;ml-rev_itlist

(dml |paired_find| 2 ml-find  
   (mk-funtyp (mk-tupletyp (mk-funtyp (|'a|) (bool)) (list (|'a|))) (|'a|)))
(de ml-find  (p l)
    (tag found (while l (let ((x (nextl l))) (if (ap p x) (*exit found x))))
	 (msg-failwith '|general| '|find|)))		;ml-find

(dml |paired_tryfind| 2 ml-tryfind 
   (mk-funtyp (mk-tupletyp (mk-funtyp (|'a|) (|'b|)) (list (|'a|))) (|'b|)))
(de ml-tryfind  (%%f %l)
    (tag found
	 (while %l (tag evaluation (*exit found (ap %%f (nextl %l)))))
	 (msg-failwith '|general| '|tryfind|)))		;ml-tryfind

(dml |paired_filter| 2 ml-filter  
   (mk-funtyp (mk-tupletyp (mk-funtyp (|'a|) (bool)) (list (|'a|))) (list (|'a|))))
(de ml-filter  (p l)
    (let ((r nil))
      (while l (let ((x (nextl l))) (if (ap p x) (newl r x))))
      (reverse r)))				;ml-filter

(dml |paired_mapfilter| 2 ml-mapfilter
  (mk-funtyp (mk-tupletyp (mk-funtyp (|'a|) (|'b|)) (list (|'a|))) (list (|'b|))))
(de ml-mapfilter (%%f %l)
    (let ((r nil)) (while %l (tag evaluation (newl r (ap %%f (nextl %l)))))
	 (reverse r)))				;ml-mapfilter

(de succeeds (%%f x)
    (tag OK (tag evaluation (ap %%f x) (*exit OK t)) nil))	;succeeds

