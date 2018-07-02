;**************************************************************************
;*
;*	L-obj
;*
;**************************************************************************
;* Original: F-obj.l (Cambridge-LCF)
; Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile)
	 (include llmac)
	 (include S-macro)
	 (genprefix obj))

;new exceptions

; discriminators
(dml |is_string| 1 ml-is_string (mk-funtyp (obj) (bool)))
(de ml-is_string (x) (eq (typep x) 'symbol))  ;ml-is_string

(dml |is_int| 1 numberp (mk-funtyp (obj) (bool)))

(dml |is_cons| 1 ml-is_cons (mk-funtyp (obj) (bool)))
(de ml-is_cons (x) (consp x))  ;ml-is_cons ;since llmacros unknown at run time

; constructors
(dml |obj_of_string| 1 Id(mk-funtyp (string) (obj)))

(dml |obj_of_int| 1 Id (mk-funtyp (int) (obj)))
(de Id (x) x)  ;Id

(dml |paired_cons| 2 cons (mk-funtyp (mk-tupletyp (obj) (obj)) (obj)))

; destructors
(dml |string_of_obj| 1 ml-string_of_obj (mk-funtyp (obj) (string)))
(de ml-string_of_obj (x)
       (if (ml-is_string x) x (msg-failwith '|general| '|string_of_obj|)))  
;ml-string_of_obj

(dml |int_of_obj| 1 ml-int_of_obj (mk-funtyp (obj) (int)))
(de ml-int_of_obj (x)
       (if (numberp x) x (msg-failwith '|general| '|int_of_obj|)))  
;ml-int_of_obj

(dml |left| 1 ml-left (mk-funtyp (obj) (obj)))
(de ml-left (x)
    (if (consp x) (car x) (msg-failwith '|syntax| '|left|)))	;ml-left

(dml |right| 1 ml-right (mk-funtyp (obj) (obj)))
(de ml-right (x)
    (if (consp x) (cdr x) (msg-failwith '|syntax| '|right|)))	;ml-right

;updators
(dml |paired_set_left| 2 ml-set_left (mk-funtyp (mk-tupletyp (obj) (obj)) (obj)))
(de ml-set_left (x y)
    (if (consp x) (rplaca x y) (msg-failwith '|syntax| '|set-left|)))	
;ml-set_left

(dml |paired_set_right| 2 ml-set_right (mk-funtyp (mk-tupletyp (obj) (obj)) (obj)))
(de ml-set_right (x y)
    (if (consp x) (rplacd x y) (msg-failwith '|syntax| '|set_right|)))	;ml-set_right

;equality
(dml |paired_eq| 2 eq (mk-funtyp (mk-tupletyp (obj) (obj)) (bool)))

;lisp eval, for communication between lisp and ml
;use with caution!
(dml |lisp_eval| 1 eval (mk-funtyp (obj) (obj)))
