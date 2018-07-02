;****************************************************************************
;*
;*	S-unix
;*
;****************************************************************************
; All unix-dependent functions reside here.
; LP - help system, directory and printing functions
; Mikael Hedlund, Rutherford Appleton Lab. (1986)
         
(eval-when (compile) 
#+ franz (include llmac)
         (special %help-dir %directory))

; Search for a filename on a list of directories (currently none)
; Return t iff present.  Side-effect:  set %directory so that of file
; Does not search for directory if filename specifies one already
(defun search-path (filename)
  (setq %directory '||)
  (probef (abs-path filename)))


; validity of file token
; must limit the file part (excluding directories) to 11 chars
; to allow for Unix's 14 char limit, and a suffix .xx
; (Unless this Unix has long filenames)
#-long-filenames
(defun filetokp (kind tok)
    (let ((chars (nreverse (exploden tok)))
	  (count 0))
	 (while (and chars (neq (nextl chars) #//)) (incr count))
	 (<= count 11)))  ;filetokp
#+long-filenames
(defun filetokp (kind tok) t)


; extensions should not exceed 2 characters
(defun fileof (kind name) 
   (selectq kind
    (theory (uconcat name '|.th|))
    (theorydata (uconcat name '|.th|))
    (theoremdata   (uconcat name '|.th|))
    (help (uconcat %help-dir '|/| name '|.hlp|))
    (kwic (uconcat %help-dir '|/| name '|.kwic|))
    (ml   (uconcat name '|.ml|))
    (lisp   (uconcat name '|_ml.l|))
    (code   (uconcat name '|_ml.o|))
    (t (lcferror (cons kind '(bad arg fileof))))
  ))  ;fileof


(defun bigger (obj size)  (> (flatc obj size) size))  ;bigger


(defun display-file (fname)
    (system (uconcat "more " fname)))

(defun keyword-search (key fname)
    (system (uconcat "fgrep '" key "' " fname " | more")))
