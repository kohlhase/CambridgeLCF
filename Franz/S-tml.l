;***********************************************************************
;*
;*	S-tml
;*	
;***********************************************************************
;top level loop
; Origin: EDINBURGH LCF (Milner,Gordon,Wadsworth...)
; Modified: CAMBRIDGE LCF (Huet,Paulson,Cousineau...) Modified: CAMBRIDGE LCF
				; (Huet,Paulson,Cousineau...  Modified:
				; CAMBRIDGE LCF (Huet,Paulson,Cousineau... 
; Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile )
  (include S-constants)
  (include llmac)
  (include S-macro)
  (genprefix tml))



;***********************************************************************
;*	PRINTRESULTS
;***********************************************************************
;print result of top level declaration or expression.
(de printresults ()
  (selectq (car %pt)
	((mk-val mk-fun mk-type mk-datatype mk-abstype mk-exception
	  mk-local mk-infix mk-infixr mk-nonfix mk-decseq)
		(printdec %pt %thistydec %thisdec %thisexdec %val %ty))
	(t (printit %val %ty))
   );end selectq
);end printresults

;***********************************************************************
;*	PRINTTIME
;***********************************************************************
; Print runtime and GC time if %time
(de printtime (final-times init-times)	
    (when prflag
      (let ((runtime (- (car final-times) (car init-times)))
	    (gctime (- (cdr final-times) (cdr init-times))))
	(let ((seconds (quotient runtime 10)))
	  (when %time
	    (llprinc '|Runtime: |)(llprinc seconds)
	    (llprinc '|.|) (llprinc (- runtime (* seconds 10)))
	    (llprinc '|s|) (llterpri))
	);end let
	#+symbolics gctime
	#-symbolics (let ((seconds (quotient gctime 10)))
		      (when %time
			(llprinc '|GC: |) (llprinc seconds)
			(llprinc '|.|) (llprinc (- gctime (* seconds 10)))
			(llprinc '|s|) (llterpri))
		    );end let1
      );end let
    );end when
); printtime

;***********************************************************************
;*		EXTEND_ENV
;***********************************************************************
;extend exn with lisp-pairs 
(de extend_env (bvs lb env)
   (cond
	((null bvs) env)
	((eq (car bvs) val);value declaration
	   (extend_val (cdr bvs) lb env))
	((eq (car bvs) exc);exception declaration
	   (extend_exc (cdr bvs) lb env))
	(t (extend_env (cdr bvs) (cdr lb)
		(extend_env (car bvs) (car lb) env)))
   );end cond
);end extend_env

;***********************************************************************
;*	EXTEND_VAL
;***********************************************************************
;extend env with (id value . %val)
(de extend_val (bvs lb env)
   (cond
	((null bvs) env)
	((atom bvs)
	   (if (eq bvs '%const);constant, ignore!
		env
		(cons `(,bvs ,lb . ,val) env)
	   ));end if
	((eq (car bvs) '%lay);layered pattern
	   (extend_val (cadr bvs) (cadr lb)
		(extend_val (caddr bvs) (caddr lb) env))) 
	((eq (car bvs) rec);recursive def.
	   (extend_val 
		(if (atom (cadr bvs));single binding
		    (cadr bvs)
		    (mapcar 'car (cdr bvs));several bindings, pick out ids
		);end if
		lb env
	   ));end
	((eq (car bvs) record);must cope with permutations
	  (let ((bvl (cdr bvs)) (e env))
	   (while bvl
	     (setq e
		   (extend_val (cdar bvl) (assoc1 (caar bvl) (cdr lb)) e)
	      );end setq
	            (setq bvl (cdr bvl))
	    );end while
	    e;return e
	   ));end let
	(t
	   (extend_val (car bvs) (car lb)
		(extend_val (cdr bvs) (cdr lb) env)))
   );end cond
);end extend_val

;***********************************************************************
;*	EXTEND_EXC1
;***********************************************************************
;extend env with (id exception-value . %exc)
(de extend_exc (bvs lb env)
   (cond
	((null bvs) env)
	((atom bvs) (cons `(,bvs ,lb . ,exc) env))
	(t (extend_exc (car bvs) (car lb)
	      (extend_exc (cdr bvs) (cdr lb) env)))
   );end cond
);end extend_exc

;***********************************************************************
;*	SET_BINDINGS
;***********************************************************************
;set unique symbols (lisp atoms) to corresponding values
(de set_bindings (lb val)
   (cond
	((null lb) nil)
	((atom lb)
	   (ifn (eq lb '%const)
		(set lb val)
	   ));end ifn
	((eq (car lb) lay); layered pattern
		(set_bindings (cadr lb) val)
		(set_bindings (caddr lb) val))
 	((eq (car lb) record);cope with mutations
	    (mapcar
		'(lambda (x) 
		    (set_bindings (cdr x) (assoc1 (car x) (cdr val)))
		);end lambda
		(cdr lb)
	    ));end mapcar
	(t (set_bindings (car lb) (car val))
	   (set_bindings (cdr lb) (cdr val)))
   );end cond
);end set_bindings

;***********************************************************************
;*	UPDATEVALUES
;***********************************************************************
;update value environment
(de updatevalues ()
   (cond
	((memq (car %pt) '(mk-type mk-datatype mk-infix mk-nonfix)) nil)
	((and (eq (car %pt) 'mk-decseq) (not new%%lb)) nil)
	(new%%lb; declaration!
	   (setq global%env (extend_env (car %val) new%%lb global%env))
	   (set_bindings new%%lb (cdr %val)))
	(t (putprop lastvalname %val 'mlval)
	   (putprop lastvalname %ty 'mlvartype))
   );end cond
);end updatevalues

;***********************************************************************
;*	EVAL-INTERRUPT
;***********************************************************************
;interrupt handler during evaluation phase.
(de eval-interrupt (X)
   (prog2 (putprop (eval (get_exc_binding 'interrupt)) 'interrupt 'exname)
	  (throw (cons 'pac (cons (eval (get_exc_binding 'interrupt))
		nil)) 'evaluation)
  );end prog2
);end eval-interrupt

;interrupt handler for all other phases
(de comp-interrupt (X)
  (print 'interrupt)(llterpri) (resetio) (tml))

;***********************************************************************
;*	EVALPR
;***********************************************************************
;evalate %pr
(de evalpr ()
   (mapc (function eval) %compfns);evaluate function definitions
   (let ((%e `(())))
	(errortrap 
	   '(lambda (errtok)
		(llprinc '|Lisp Error During Evaluation, Please Report!|)
		(llterpri)
		(llprinc '|Stack Dump: |)
		(llterpri)
		(showstack); print out the stack for info
		(llterpri)
		(failwith 'lisperror); raise SML exception
	    );end lambda
	    (eval %pr);evaluate !
	);end errortrap
   );end let
);end evalpr
   
;***********************************************************************
;*	PARSEML0 TYPECHPT TRANPT
;***********************************************************************
(de parseml0 () (gnt) (parse_ml 37));parse top level construction (generates parse tree)
(de typechpt () (typecheck %pt)); type-check (generates internal repr. of type)
(de tranpt () (let ((%p `(()))) (tran %pt))); translate to lisp (generates lisp code)

;***********************************************************************
;*	OKPASS
;***********************************************************************
;parse,typecheck,translate or evaluate and catch any errors
(de okpass (pass)
   (tag ok
	(let ((b 
	   (selectq pass
		(parse
		   (tag parse (setq %pt (parseml0)) (*exit ok t)))
		(typecheck 
		   (tag typecheck (setq %ty (typechpt)) (*exit ok t)))
		(translation 
		   (tag translation (setq %pr (tranpt)) (*exit ok t)))
		(evaluation 
		   (tag evaluation (setq %val (evalpr)) (*exit ok t)))
	     );end selectq
	      ));end b
	   (cond ((eq (car b) 'pac);package returned!
		(llterpri)
		(llprinc (concat 
		  '|exception raised: |
		   (get (cadr b) 'exname))
		);end llprinc
		;check if exception name is within scope at top level:
		(let ((exn (get (cadr b) 'exname)))
		   (cond 
		     ((not (equal (eval (get_exc_binding exn)) (cadr b)))
		        (llterpri)
			(llprinc (concat
	'|Warning: exception "| exn
	'|" was caught at top level, but is out of scope|
		        )));end llprinc
		      (t
			(llprinc '| with |)
			(if (cddr b);exception raised with expression
			    (let ((print_code 
				`((lambda (a) 
				   ,(tr_print 'a (get_exntyp exn) nil)(pnewline))
				  ',(cddr b)))); apply value to print function
				    (eval print_code)
			     );end let
			     (llprinc '|()|);else unit
			));end if
		    );end cond
		 );end let
	         (llterpri))
	   );end cond	    
	   (llprinc 
		(selectq pass
		   (parse '|parse|)
		   (typecheck '|typecheck|)
		   (translation '|translation|)
		   (evaluation '|evaluation|)
		   (evtmlop '|evaluation|)
		);end selectq
	    );end llprinc
	    (llprinc '| failed |)
	    (llterpri)
	    (space)
	    (llterpri)
	    (ifn (memq %f '(load compile))
		(*exit tmllooptag %f))
;;; propagate failure if performing load or compile
	   (putprop lastvalname () 'mlval)	;to prevent abscope type
	   (putprop lastvalname '(mk-recordtyp) 'mltype)	
	   (infilepop)				;flush input file
	   (*exit loaderror nil)
     );end let
   );end tag
);end okpass

(de eval-remember (x)
    (when %outport (print-file x))
    (eval x))					;eval-remember

;***********************************************************************
;*	TML
;***********************************************************************
;initialize and call top level loop
(de tml ()
   (let ((base 10) (ibase 10) (*nopoint t) 
	 (%timestamp (mod (clock) 10000)))
	(init-io);franz.l
	(banner);site.l
	(incr %symcount (mod %timestamp 100))
        (signal 2 'comp-interrupt);set lisp interrupt handler
	(tag eof (tmlloop))
        (cond ((not %notcmnt) (llprinc '|Warning: unmatched comment brackets |)
			      (llterpri)))
	(finalize-tml)
    );end let
);end tml

(de top%f () (memq %f '(() load compile)))

;******************************************************************************
;*	TMLLOOP
;******************************************************************************
;top level loop
(defun tmlloop ()
  (initlean)			; init parser only once!!
  (while t
    (tag tmllooptag
      (and prflag (top%f) (llterpri))
      (defconst prompt_char #/!);prompt changed in parse
      (let ((%thisdec ()) (%thistydec ()) (%thisexdec ())
	    (%constr ()) (%inf ()) (fun%env nil)
	    (%coneq_l) (%eq_flg) (%eq_flg1) (%generic))
	 (typeinit)
	 (okpass 'parse)			;parse
	 (setq %head (car %pt))
	 (okpass 'typecheck)		;typecheck
	 (okpass 'translation)		;translate
	 (let ((init-time (runtime10th)))
	      (signal 2 'eval-interrupt); set lisp interrupt handler
	      (okpass 'evaluation)		;evaluate
	      (signal 2 'comp-interrupt);back to default for interrupt handler
	      (let ((final-time (runtime10th)))
		   (update_inf)			;update infixes
		   (update_cons)			;update constructors
		   (updatetypes)			;update types
		   (updatevalues)			;update values
		   (printresults)			;print results
		   (printtime final-time init-time)
  ))))))			; tmlloop

(dml |load| 2 ml-load (mk-funtyp (mk-tupletyp (string) (bool)) (mk-recordtyp)))

;******************************************************************************
;*	ML_LOAD
;******************************************************************************
;load,parse,typecheck,translate,evaluate ml file.
(de ml-load (tok prflag)
    (let ((oldpiport piport) (%f 'load) (%dump ()))
      (when prflag (llterpri)(llprinc '|loading ...|)
		  (llterpri))
      (tag eof
	   (tag loaderror			; catch failures inside load
		(cond  ((not (filetokp 'ml tok))
		     (llprinc (concat tok '| cannot be a file name|))
		     (msg-failwith '|general| 'load)))
		#-lelisp       (if (fileexists 'code tok)
				   (*exit eof (load (abs-path (fileof 'code tok)))))
		(cond ((not (fileexists 'ml tok))
		     (llprinc (concat tok '| not found|))
		     (msg-failwith '|general| 'load )))
		(infilepush (abs-path (fileof 'ml tok)))
		(let ((%pt ()) (%ty ()) (%pr ()) (%val ()) (%head ()) (new%%lb ()))
		  (tmlloop)
		);end let
	   );end tag
           ;an error occurred during file load
	   (msg-failwith '|general| 'load )
       );end tag eof
       (cond ((not %notcmnt) (llprinc '|Warning: unmatched comment brackets |)
			      (llterpri)))
					;reached end of file without errors
      (unless (eq piport oldpiport) (infilepop))
      (when prflag
	(llprinc '|file loaded: |) (llprinc tok)
	(llterpri)))
);ml-load

(dml |compile| 2 ml-compile (mk-funtyp (mk-tupletyp (string) (bool)) (mk-recordtyp)))
 

;******************************************************************************
;*	ML-COMPILE
;******************************************************************************
;load and comile ml file.
(de ml-compile (tok prflag)
    (let ((piport piport)
	  (inputstack inputstack)
	  (%f 'compile)
	  (%dump ())
	  ($gcprint ())
	  (filename (fileof 'lisp tok)))
      #+lelisp (msg-failwith 'compile '|use load in lelisp|)
      (when prflag (llterpri)(llprinc '|compiling ... |)
	           (llterpri))
      (tag eof
	   (tag loaderror
		(cond  ((not (filetokp 'ml tok))
		     (llprinc (concat tok '| cannot be a file name|))
		     (msg-failwith '|general| 'load)))
		(cond ((not (fileexists 'ml tok))
		     (llprinc (concat tok '| not found|))
		     (msg-failwith '|general| 'load )))
		(infilepush (abs-path (fileof 'ml tok)))
		(setq %outport (outfile filename))
		(print-file '(declare (special %vtyl)))
		;interpreted code contains macros so include in lispfile:
		(let ((%pt ()) (%ty ()) (%pr ()) (%val ()) (%head ()))
		   (compiloop))
	    );end tag
;;; an error has occurred during compilation
	   (close %outport)
	   (msg-failwith '|general| 'compile)
      );end tag
      (cond ((not %notcmnt) (llprinc '|Warning: unmatched comment brackets |)
			      (llterpri)))
;;; no error occurred
      (close %outport)
      (infilepop)
      (setq poport ())			;necessary
      (setq %outport ())
      (compile-lisp filename)		;call Lisp compiler - System dependent
      (when prflag
	(llterpri) (llprinc tok)
	(llprinc '| compiled successfully|) (llterpri)))
);end ml-compile

;******************************************************************************
;*	COMPILOOP
;******************************************************************************
(de compiloop ()
  (while t
    (let ((%thisdec ()) (%thistydec ()) (%thisexdec ()) (%constr ())
	  (%inf ()) (fun%env ()) (%coneq_l ()) (%eq_flg ())
	  (%eq_flg1 ()) (%generic ()) (new%%lb ()))
      (and prflag (top%f) (let ((poport ())) (llterpri)))
      (initlean)
      (okpass 'parse)
      (setq %head (car %pt))
      (okpass 'typecheck)
      (okpass 'translation)
      (okpass 'evaluation)
      (update_inf)
      (update_cons)
      (updatetypes)
      (updatevalues)
      (let ((poport ())) (printresults))
      (mapc '(lambda (fn) (print-file fn)) %compfns)
      (print-file
        `(execute ',%pt ',%ty ',%thisdec ',%thistydec ',%thisexdec ',%head ',new%%lb ',%pr)
      );end print-file
   );end let
  );end while
);end compiloop

;******************************************************************************
;*	EXECUTE
;******************************************************************************
;evaluate lisp code and update
(de execute (%pt %ty %thisdec %thistydec %thisexdec %head new%%lb %pr)
    (and prflag (top%f))
    (let ((init-time (runtime10th)))
      (okpass 'evaluation)
      (let ((final-time (runtime10th)))
	(update_inf)
	(update_cons)
	(updatetypes)
	(updatevalues)
      );emd let
    );end let
);end execute


;*********************************************************************
;initialize global variables

(setq fin-ligne t)
(setq %generic nil)
(setq %eq_flg nil)
(setq %eq_flg1 nil)
(setq %coneq_l nil)
(setq fun%env nil)
(setq %p nil)
(setq %e nil)
(setq %mult_l nil)
(setq %vartypes nil)
(setq %symcount 10)
(setq %tyvar_l nil)
(setq type%errors 0)
(setq %emt nil)
(setq %exemt nil)
(setq %temt nil)
(setq asscheck nil)
(setq env nil)
(setq tenv nil)
(setq exenv nil)
(setq %sections nil)
(setq %thisdec nil)
(setq %thistydec nil)
(setq %thisexdec nil)
(setq %printfns nil)
(setq %stringfns nil)
(setq %skiplimit 30)
(setq %overload nil)
(setq %eqtypes nil)
(defconst lastvalname '|it|)
(setq %notcmnt t)
(signal 2 'comp-interrupt)

(dml |save| 1 ml-save (mk-funtyp (string) (mk-recordtyp)));save core
(dml |quit| 0 quit (mk-funtyp (mk-recordtyp) (mk-recordtyp)));quit lisp

(when initial%load 
   (setq %f ())
   (setq %sections ())
   (setq %time ())
   (setq %outport ())
);end when

(dml |lisp| 1 ml-lisp (mk-funtyp (string) (mk-recordtyp)))
 
(de ml-lisp (tok)
    (errortrap '(lambda (errtok) (failwith 'lisperror))
	       #-lelisp	 (eval (readlist (explodec tok)))
	       #+lelisp  (eval (implode (explode tok)))
    );end eertrap
); ml-lisp

(de lcferror (s) (llprinc "LCF system error: ") (llprinc s) (llterpri)
                 (llprinc "Please report !") (llterpri)
		 (llprinc "Stack Dump: ") (llterpri)
		 (showstack)
		 (failwith 'lisperror)
);end


(dml |timer| 1 ml-timer (mk-funtyp (bool) (mk-recordtyp)))
(de ml-timer (fl) (setq %time fl))
