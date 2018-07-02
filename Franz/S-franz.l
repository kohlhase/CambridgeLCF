;****************************************************************************
;*
;*	S-franz
;*
;****************************************************************************
;
;Changes made 16/7/85: deletef - (sys:unlink file) -> (syscall 10 `file)
;(4.2 ->  4.1)	       clock   - (sys:time) -> (syscall 13)
;		       setdebug- `sys:int-serv -> `INT
; Mikael Hedlund, Rutherford Appleton Lab. (1986)
 
(eval-when (compile)
     (include llmac)
     (include S-macro)
     (special user-top-level ER%all $gcprint prinlength prinlevel
	%outport %std-input fin-ligne %debug
	poport piport inputstack outfiles ibase lf))
 
; the scanner functions
(synonymq imploden implode)
(synonymq printint exploden)
 
; Renaming necessary since infile is very special in maclisp
(synonymq filein infile)
(synonymq consp dtpr)
 
; the function "quit" terminates the session
(putd 'quit (getd 'exit))
 
;*****************************************************************************
; LCF must die upon receiving the hangup signal (HUP)
; otherwise LCF jobs started under Emacs will remain around causing havoc
(signal 1 'quit)
 
(putd 'backtrace (getd 'baktrace))
 
; catenate a list of things into a STRING
(de catenate l (get_pname (apply 'uconcat l)))   ; lexpr
 
(defun readint (l) (readlist (mapcar (function ascii) l)))  ; readint
 
(defun readcn (port)
   (let ((char (readc port)))
	(if char (cascii char))))  ;readcn
 
; the ascii code of symbol a
(defun cascii (a) (getcharn a 1))  ; cascii
 
;*****************************************************************************
; the IO functions
 
(defun llterpri () (terpri poport))  ;llterpri
 
(defun llprinc (expr) (princ expr poport))  ;llprinc
 
(defun llprint (expr) (print expr poport))  ;llprint
 
(defun llreadcn () (readcn piport))  ; llreadcn
 
(defun llread () (read piport))  ; llread
 
(defun input (channel) channel)  ; input
 
(defun deletef (file) (sys:unlink file));deletef, changed from (sys:unlink file)
 
; Restore previous input file after closing current one
(defun infilepop ()
    (close piport)
    (setq piport (nextl inputstack)))    ; infilepop
 
 
; get absolute time (since 1970) for time-stamps
(defun clock () (sys:time));changed from (sys:time)
 
(defun system (cmd)  (apply 'process (list cmd)))
 
;*****************************************************************************
;*	COMPILE-LISP
;*****************************************************************************
; call Lisp compiler from Lisp (for compiling ML)
(defun compile-lisp (filename)
    (let ((command (concat "liszt -w -q " filename)))
         (princ "calling lisp compiler ...") (terpri)
         (let ((result (system command)))
	    (if (zerop result) (ifn %debug (deletef filename))
	        (msg-failwith '|general| 'compile ))))
)  ;compile-lisp
 
 
(setq %std-input piport)	; for flushing tty
 
;*****************************************************************************
;*	ML-SAVE
;*****************************************************************************
(defun ml-save (tok)
    (gc)
    (let ((user-top-level 'drain-tml))
         (apply 'dumplisp (list tok)))
)  ;ml-save
 
;*****************************************************************************
;*	HANDLE-INTERRUPT
;*****************************************************************************
; to allow user to stop LCF without descending to Lisp
; called when user hits interrupt key
(defun handle-interrupt (signal-number)
    (terpri) (princ "process interrupted")
    (reset))  ; handle-interrupt
 
 
;*****************************************************************************
;*	SETDEBUG
;*****************************************************************************
; Turn debugging on/off
; sets Lisp debugging switches, interrupt handler, and top-level
(defun setdebug (flag)
 (cond
  (flag
     (debugging t)
     (setq $gcprint t)		; monitor garbage collections
     (setq prinlength 6)   	; control printing of circular lists
     (setq prinlevel 4)
     (sstatus translink nil)
     (signal 2 'sys:int-serv)		; restore Franz interrupt handler
     (setq user-top-level nil))
  (t (sstatus translink on)
     (setq $gcprint nil)
     (setq prinlength nil)
     (setq prinlevel nil)
     (setq ER%all nil)		; remove error handler
     (*rset nil)
     (signal 2 'handle-interrupt)
     (setq user-top-level 'tml))))  ;setdebug
 
 

;*****************************************************************************
;*	FINALIZE-TML
;*****************************************************************************
; Function called before returning to Lisp
; Clears user-top-level to prevent automatic re-entry to ML
(defun finalize-tml ()
   (setdebug t) (reset))		; finalize-tml
 
 
;*****************************************************************************
;*	SETUP
;*****************************************************************************
; Turn off debugging switches and set top level to (tml)
(defun setup nil
    (setdebug nil)
    (allocate 'list 500) 	; to help gc problems  ; only for LCF
    (reset))  ;setup
 
;*****************************************************************************
;*	SETUP-ML
;*****************************************************************************
(defun setup-ml nil
    (setdebug nil)
    (reset))  ;setup-ml
 
;*****************************************************************************
;*	SET-MAKE
;*****************************************************************************
; set up batch loading of system via Makefile
(defun set-make () (setq ER%all 'make-err-handler)) ; set-make
 
 
;*****************************************************************************
;*	MAKE-ERR-HANDLER
;*****************************************************************************
; report error to log file and abort job
(defun make-err-handler (msg)
    (princ '|error during loading of system:|)(terpri)
    (let (((type id cont string . data) msg))
       (princ string)
       (mapc '(lambda (x) (princ '| |) (print x)) data)
       (terpri)
       (baktrace)
    (quit 1)))			; make-err-handler
 
 
; get the date as a string
(defun date nil  (substring (status ctime) 5 6)) ; date
 
; no in-session compilation in Franz
(defun lisp-compile (l) nil) 	; lisp-compile
 
(defun make-catch (body tag) `(catch ,body ,tag))
(defun make-throw (body tag) `(throw ,body ,tag))
 
; standard flatc does not work on bignums
(defun flatsize2 (str)
   (if (bigp str) (length (explodec str)) (flatc str)))
 
 
; Returns (jobtime . gctime) where jobtime does not include gctime
; Unix -- return current runtime in 10ths of seconds (rounded)
; Depends on line frequency
(defun runtime10th ()
          (let (((proc gc) (ptime)))
		(cons (quotient (- proc gc) 6) (quotient gc 6)))) ;runtime10th
 
(defun bigger (obj size)  (> (flatc obj size) size))  ;bigger
 
 
; throws away junk left in Make commands (stupid Franzlisp!)
(defun drain-tml () (drain %std-input) (setq fin-ligne t) (tml))
 
(defun init-flags ()
   (setq ibase 10))  ; init-flags
 
;*****************************************************************************
;*	INIT-IO
;*****************************************************************************
(defun init-io ()
    (setq piport nil)
    (setq poport nil)
    (setq outfiles nil)
    (setq inputstack nil)
    (setq %outport nil))  ; init-io
 
(defun list2string (chl) (get_pname (imploden chl)))
 
(defun ml-int_of_string (s)
  (errortrap '(lambda (x) (failwith "int_of_string"))
     (let ((n (readlist (exploden s))))
        (unless (fixp n) (failwith "int_of_string"))
	n))
); ml-int_of_string
 

