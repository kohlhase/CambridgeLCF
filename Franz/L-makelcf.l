;****************************************************************************
;*
;*	S-makelcf
;*
;****************************************************************************
;* Original: F-makelcf (Cambridge LCF)
; Modified for Standard ML by Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile) (special initial%load experimental %debug))

(setq %system-name "Cambridge LCF ") 
(setq %version "(RAL 1.6)") 


(setq %debug nil)
(setq %mlprintdepth 3)

; operating system ?
#+unix (load "S-unix") 
#+Multics (load "S-multics")

; Lisp system?
#+franz (load "S-franz")
#+psl (load "S-psl")
#+lelisp (load "S-lelisp")

(setq experimental nil)
(cond (experimental (experimental-init) (load "S-ol-rec")))

(setq eof '$eof$)
(setq %mlprindepth 3)

(setq initial%load t)	; allow modules to initialize themselves

;load SML object files:
;(load 'llmac)
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


;load LCF object files:

(load 'L-dlcf)
(load 'L-ol-syntax)
(load 'L-ol-rec)
(load 'L-typeol)
(load 'L-parsol)
(load 'L-writol)
(load 'L-subst)
(load 'L-inst)
(load 'L-thyfns)
(load 'L-ol-net)
(load 'L-simpl)

(setq initial%load nil)	  ; patching does not cause re-initialization

(cond ((fileexists 'theorydata 'PPLAMB)
    (deletef (fileof 'theorydata 'PPLAMB))))



