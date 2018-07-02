;;*****************************************************************************
;*
;*	S-makeml
;*
;*;***************************************************************************
; load ml system
; Origin: EDINBURGH LCF (Milner,Gordon,Wadsworth...) 
; Modified: CAMBRIDGE LCF (Huet,Paulson,Cousineau...) 
; Mikael Hedlund, Rutherford Appleton Lab. (1986)

(setq %system-name "Standard ML ")
(setq %version "(RAL 1.6)")

(setq prflag t );print flag

; operating system ?
#+unix (load "S-unix") 
#+Multics (load "S-multics")

; Lisp system?
#+franz (load "S-franz")
#+psl (load "S-psl")
#+lelisp (load "S-lelisp")

(setq eof '$eof$)
(setq %mlprintdepth 3)

(setq initial%load t)	; allow modules to initialize themselves

;*****************************************************************************
;load lisp files

(load 'S-macro)
(load 'S-site)
(load 'S-franz)
(load 'S-unix)
(load 'S-gp)
(load 'S-parser)
(load 'S-print)
(load 'S-dml)
(load 'S-help)
(load 'S-format)
(load 'S-type)
(load 'S-tran)
(load 'S-iox-stand)
(load 'S-list)
(load 'S-obj)
(load 'S-tml)

;*****************************************************************************
(eval-when (compile) (special initial%load experimental %debug))
(setq initial%load nil)	; patching does not cause re-initialization
