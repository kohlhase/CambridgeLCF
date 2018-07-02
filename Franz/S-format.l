;****************************************************************************
;*
;*	S-format 
;*
;****************************************************************************
;pretty printer
; Origin: CAMBRIDGE LCF (Paulson) 
; Modified: Mikael Hedlund, Rutherford Appleton Lab. (1986)

; method based on
; Oppen, Derek C., "Pretty Printing",
;      Technical report STAN-CS-79-770, Stanford University, Stanford, CA.
;      Also in ACM TOPLAS, October 1980, P. 465.

(eval-when (compile)
         (include llmac)
	 (include S-macro)
	 (include S-constants)
	 (macros t)
	 (genprefix format))

; constant definitions
(defconst %margin 72)				;right margin
(defconst %infinity 999999)			;large value for default token size

; global variables
(defvar %max-depth 30)				;max be re-set by user

; %space		; space remaining on this line
; %left-total		; total width of tokens already printed
; %right-total		; total width of tokens ever put in queue
; %pstack 		; printing stack with indentation entries
; %prettyon		; indicates if pretty-printing is on
; %curr-depth		; current depth of "begins"
; %max-depth		; max depth of "begins" to print

;*****************************************************************************
; data structures
; a token is one of
;    ('string  text)
;    ('break   width  offset)
;    ('begin   indent  [in]consistent )
;    ('end)
(defmacro tok-class (tok) `(car ,tok))
(defmacro get-string-text (tok) `(cadr ,tok))
(defmacro get-break-width (tok) `(cadr ,tok))
(defmacro get-break-offset (tok) `(caddr ,tok))
(defmacro get-block-indent (tok) `(cadr ,tok))
(defmacro get-block-break (tok) `(caddr ,tok))


;*****************************************************************************
; the Scan Stack
; each stack element is (left-total . qi)
;   where left-total the value of %left-total when element was entered
;   and qi is the queue element whose size must later be set 
(defmacro make-ss-elem (left qi) `(cons ,left ,qi))
(defmacro get-left-total (x) `(car ,x))
(defmacro get-queue-elem (x) `(cdr ,x))


;*****************************************************************************
; the Queue
; elements (size token len)   
(defmacro make-queue-elem (size tt len) `(list ,size ,tt ,len))
(defmacro get-queue-size (q) `(car ,q))
(defmacro get-queue-token (q) `(cadr ,q))
(defmacro get-queue-len (q) `(caddr ,q))
(defmacro put-queue-size (q size) `(rplaca ,q ,size))


;*****************************************************************************
; the Printing Stack, %pstack 
;  each element is (break . offset)
(defmacro get-print-break (x) `(car ,x))
(defmacro get-print-indent (x) `(cdr ,x))


;*****************************************************************************
;*	PUSH-PRINT-STAVK
;*****************************************************************************
(de push-print-stack (break offset)
    (newl %pstack (cons break offset)))


;*****************************************************************************
;*	PRINT-BLANKS
;*****************************************************************************
; print n blanks
(de print-blanks (n)
    (do ((i n (1- i))) ((eq i 0)) (llprinc '| |)))


;*****************************************************************************
;*	PRINT-TOKEN
;*****************************************************************************
; print a token
(de print-token (tt size)
  (selectq (tok-class tt)
    (string  (llprinc (get-string-text tt)) (decr %space size))
    (begin
     (let ((offset (- %space (get-block-indent tt)))
	   (brtype (if (and %prettyon (> size %space)) 
		       (get-block-break tt)
		       'fits)))
       (push-print-stack brtype offset)))
    (end (nextl %pstack))
    (break
      (selectq (get-print-break (car %pstack))
	(consist (break-new-line tt))
	(inconsist
	   (if (> size %space) (break-new-line tt) (break-same-line tt)))
	(fits (break-same-line tt))
	(t (lcferror '|bad break in pretty printer|))))
    (t (lcferror (cons tt '(bad print-token type))))))	; print-token

;*****************************************************************************
;*	PRINT-NEW-LINE
;*****************************************************************************
; print a break, indenting a new line
(de break-new-line (tt)
    (setq %space (- (get-print-indent (car %pstack)) (get-break-offset tt)))
    (llterpri)
    (print-blanks (- %margin %space)))		; break-new-line

;*****************************************************************************
;*	PRINT-SAME-LINE
;*****************************************************************************
; print a break that fits on the current line
(de break-same-line (tt)
  (let ((width (get-break-width tt)))
    (decr %space width)
    (print-blanks width)))			; break-same-line

; routines for scan stack
; determine sizes of blocks

;*****************************************************************************
;* 	CLEAR-SCAN-STACK
;*****************************************************************************
(de clear-scan-stack ()
    (setq %scan-stack (list (make-ss-elem -1 nil))))	; clear-scan-stack

;*****************************************************************************
;*	SCAN-PUSH
;*****************************************************************************
(de scan-push ()
    (newl %scan-stack (make-ss-elem %right-total (car %qright))) nil)	; scan-push

;*****************************************************************************
;*	SCAN-POP
;*****************************************************************************
; Pop scan stack and return its value of %qright
(de scan-pop () (get-queue-elem (nextl %scan-stack)))	; scan-pop

;*****************************************************************************
;*	SCAN-EMPTY
;*****************************************************************************
; test if scan stack contains any data that is not obsolete
(de scan-empty  ()
   (< (get-left-total (car %scan-stack)) %left-total))	; scan-empty

;*****************************************************************************
;*	SCAN-TOP
;*****************************************************************************
; return the kind of token pointed to by the top element of the scan stack
(de scan-top ()
    (tok-class (get-queue-token (get-queue-elem (car %scan-stack)))))	; scan-top

;*****************************************************************************
;*	CLEAR-QUEUE
;*****************************************************************************
; the queue
; size is set when the size of the block is known
; len is the declared length of the token
(de clear-queue ()
    (setq %left-total 1)
    (setq %right-total 1)
    (setq %qleft nil)
    (setq %qright nil))		; clear-queue

;*****************************************************************************
;*	ENQUEUE
;*****************************************************************************
; perhaps should use a dummy list header so %qleft is never nil
(de enqueue (tt size len)
     (incr %right-total len)
     (let ((newcell (ncons (make-queue-elem size tt len))))
       (if %qleft (rplacd %qright newcell) (setq %qleft newcell))
       (setq %qright newcell)))			; enqueue


;*****************************************************************************
;*	ADVANCE-LEFT
;*****************************************************************************
; Print if token size is known or printing is lagging
; Size is known if not negative
; Printing is lagging if the text waiting in the queue requires
;   more room to print than exists on the current line
(de advance-left ()
      (while (and %qleft
		  (or (not (< (get-queue-size (car %qleft)) 0))
		      (> (- %right-total %left-total) %space)))
	     (let (((size token len) (nextl %qleft)))
	       (print-token token (if (< size 0) %infinity size))
	       (incr %left-total len))))	; advance-left

;*****************************************************************************
;*	SETSIZE
;*****************************************************************************
; set size of block on scan stack
(de setsize (tok)
  (cond ((scan-empty) (clear-scan-stack))
	((eq (scan-top) tok)
	 (let ((qi (scan-pop)))
	    (put-queue-size qi (+ %right-total (get-queue-size qi))))))
  nil)						; setsize


; *************************************************************
; procedures to control prettyprinter from outside

; the user may set the depth bound %max-depth
; any text nested deeper is printed as the character &


;*****************************************************************************
;*	PSTRINGLEN
;*****************************************************************************
; print a literal string of given length
(de pstringlen (str len)
   (if (< %curr-depth %max-depth) (enqueue-string str len)))	; pstringlen

;*****************************************************************************
;*	ENQUEUE-STRING
;*****************************************************************************
(de enqueue-string (str len)
    (enqueue `(string ,str) len len)
    (advance-left))		; enqueue-string

;*****************************************************************************
;*	PSTRING
;*****************************************************************************
; print a string
(de pstring (str)
    (pstringlen str (flatsize2 str))); pstring

;*****************************************************************************
;*	PBEGIN-BLOCK
;*****************************************************************************
; open a new block, indenting if necessary
(de pbegin-block (indent break)
  (incr %curr-depth)
  (cond ((< %curr-depth %max-depth)
         (enqueue `(begin ,indent ,break) (- 0 %right-total) 0)
         (scan-push))
	((eq %curr-depth %max-depth)
	 (enqueue-string '& 1))))  ; pbegin-block

;*****************************************************************************
;*	PBEGIN
;*****************************************************************************
; special cases: consistent, inconsistent
(de pbegin (indent) (pbegin-block indent 'consist))  ; pbegin
(de pibegin (indent) (pbegin-block indent 'inconsist))  ; pibegin

;*****************************************************************************
;*	PEND
;*****************************************************************************
; close a block, setting sizes of its subblocks
(de pend ()
  (when (< %curr-depth %max-depth)
	(enqueue '(end) 0 0)
	(setsize 'break)
	(setsize 'begin))
  (decr %curr-depth))		; pend

;*****************************************************************************
;*	PBREAK
;*****************************************************************************
; indicate where a block may be broken
(de pbreak (blankspace offset)
  (when (< %curr-depth %max-depth)
	(enqueue `(break ,blankspace ,offset)
		 (- 0 %right-total)
		 blankspace)
	(setsize 'break)
	(scan-push)))  ; pbreak


;*****************************************************************************
;*	PINIT
;*****************************************************************************
; Initialize pretty-printer.
(de pinit ()
    (clear-queue)
    (clear-scan-stack)
    (setq %curr-depth 0)
    (setq %space %margin)
    (setq %prettyon t)
    (setq %pstack nil)
    (pbegin 0))	; pinit

;*****************************************************************************
;*	SETPRETTY
;*****************************************************************************
; Turn formatting on or off
;   prevents the signalling of line breaks
;   free space is set to zero to prevent queuing of text
(de setpretty (pp)
    (setq %prettyon pp)
    (if pp (setq %space %margin)
	   (setq %space 0)))  ; setpretty

;*****************************************************************************
;*	PNEWLINE
;*****************************************************************************
; Print a new line after printing all queued text
(de pnewline ()
    (pend)
    (setq %right-total %infinity)
    (advance-left)
    (llterpri)
    (pinit)) ; pnewline

;*****************************************************************************
;*	ML-SET_PRETTYMODE
;*****************************************************************************
; Print all remaining text in queue.
; Reinitialize (or turn off) prettyprinting
(de ml-set_prettymode (pp)
    (pnewline)
    (setpretty pp))  ; ml-set_prettymode

(pinit)
(setpretty t)

;*****************************************************************************
;*	ML-MAX_PRINT_DEPTH
;*****************************************************************************
(de ml-max_print_depth (md)
  (setq %max-depth md))		; ml-max_print_depth

(dml |max_print_depth| 1 ml-max_print_depth (mk-funtyp (int) (mk-recordtyp)))

(dml |set_prettymode| 1 ml-set_prettymode (mk-funtyp (bool) (mk-recordtyp)))
(dml |print_newline| 0 pnewline (mk-funtyp (mk-recordtyp) (mk-recordtyp)))
(dml |print_begin| 1 pbegin (mk-funtyp (int) (mk-recordtyp)))
(dml |print_ibegin| 1 pibegin (mk-funtyp (int) (mk-recordtyp)))
(dml |print_end| 0 pend (mk-funtyp (mk-recordtyp) (mk-recordtyp)))
(dml |print_break| 2 pbreak (mk-funtyp (mk-tupletyp (int) (int)) (mk-recordtyp)))
