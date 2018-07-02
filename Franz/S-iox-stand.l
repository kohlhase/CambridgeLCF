 
;*******************************************************************************
;*
;*		S-iox-stand 
;*
;*******************************************************************************
;input/output
; Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile)
  (include S-constants)
  (include llmac)
  (include S-macro)
  (genprefix iox)
  (*lexpr concat uconcat))
 
;*****************************************************************************
;*	PRINT-FILE
;*****************************************************************************
; print on an output file, setting output parameters properly
; use channel %outport if set
(de print-file  (x)
    (let ((prinlevel nil) (prinlength nil) (poport (or %outport poport)))
      (llprint x) (llterpri)))			; print-file
 
 
;*****************************************************************************
;*	PROTECTIO
;*****************************************************************************
;  Part 1: protectio  formerly in module din
(de protectio (%%%fn %%%args)
    (let ((inputstack inputstack) (outfiles outfiles)
	  (piport piport) (poport poport))
      (apply %%%fn %%%args)))			;NEW protectio
 
;*****************************************************************************
;*	IDENP
;*****************************************************************************
;  Part 2: Predicates on tokens
(de idenp (tok)
    (let ((l (ml-explode tok)))
      (and l
	   (letterp (cascii (car l)))
	   (forall 'alphanump (mapcar 'cascii (cdr l))))))	;idenp
  
;*****************************************************************************
;*	NEXTCN
;*****************************************************************************
; Part 3 : terminal input
(de nextcn ()
    (ifn piport (cond (fin-ligne (tyo prompt_char)(tyo space)(setq fin-ligne nil))))
    (let ((c (llreadcn)))
      (ifn c (*exit eof nil))
      (cond  ((eq c lf) 
         (setq fin-ligne t)))
      c)
);nextcn
 
 
;*****************************************************************************
;*	FILEEXISTS
;*****************************************************************************
;  Part 4:  file token handling and file opening, closing, etc
(de fileexists (kind tok)
    (protectio (function (lambda (kind tok)
			   (search-path (fileof kind tok))))	;NEW   sets %directory
	       (list kind tok)))		;fileexists
 
;*****************************************************************************
;*	ABS-PATH
;*****************************************************************************
(de abs-path (path) (uconcat %directory path))	;abs-path
 
;*****************************************************************************
;*	INFILE-PUSH
;*****************************************************************************
; Re-direct input from terminal to given file
; inputstack holds all previous values of piport
(de infilepush (filespec)
    (newl inputstack piport)
    (setq piport  (filein filespec)))		; infilepush
 
;*****************************************************************************
;*	FILEDELETE
;*****************************************************************************
(de filedelete (kind tok)
    (and (eq kind 'draft)
	 (protectio
	   (function (lambda (kind tok)
		       (deletef (fileof kind tok))
		       (terpri) (princ (list kind tok 'deleted))(terpri)
		       ))
	   (list kind tok))))		;filedelete
 
;*****************************************************************************
;  Part 5:  output for terminal.
(de space () (llprinc '| |))			; space

