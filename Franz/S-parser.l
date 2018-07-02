;**********************************************************************
;*                                                                    *
;* 	PARSER 							      *
;*                                                                    *
;*CONVENTION: ML_CONSTRUCT (upper case) is defined as the result of   *
;*    	      parsing ml_construct (lower case).		      *
;*								      *
;**********************************************************************
; Origin: EDINBURGH LCF (Milner,Gordon,Wadsworth...) 
; Modified: CAMBRIDGE LCF (Huet,Paulson,Cousineau...) 
; Mikael Hedlund, Rutherford Appleton Lab. (1986)
;*
;*
;*

(eval-when  (compile )
(include S-constants)
(include llmac)
(include S-macro))

(eval-when (compile eval)
  (defmacro bounded (lower a upper) 
    `(and (<= ,lower ,a)(<= ,a ,upper))))	; bounded


;**********************************************************************
;* 	Definitions                                                   
;**********************************************************************

(defconst sharp_chr #/#)
(defconst uparrow #/^)
(defconst mulchr #/*)
(defconst lrecordchr #/{)
(defconst rrecordchr #/})
(defconst prime #/')
(defconst space #/ )
(defconst cr  13) ;carriage return
(defconst lf  10) ;line feed
(defconst tab 9)  ;tab
(defconst lparen #/()
(defconst rparen #/))
(defconst period #/.)
(defconst comma #/,)
(defconst colon #/:)
(defconst scolon #/;)
(defconst lbrkt #/[)
(defconst rbrkt #/])
(defconst multiply #/*)
(defconst tokqt #/")
(defconst escape #/\)
(defconst neg_tok #/~)
(defconst inf_lev 550);infixed prec_lev.

;symols allowed in symbolic id's.
(defconst id_syms
	'(|!| |%| |&| |$| |+| |-| |/| |:| |<| |=| |>| |?| |@| 
	  |\\| |~| |\|| |*|))

;predefined type consructors
(defconst tycons '(unit bool int string type term ; real is also a func.
		   form thm list));and ref is also a value constructor !
				  ;hence, not included!

; Meta language symbols
(defconst tml_sym '|;|)
(defconst dereference_sym '|!|)
(defconst assign_sym '|:=|)
(defconst lcmnt_sym '|(*|); comment sym.
(defconst rcmnt_sym '|*)|); - " -
(defconst sharp_sym '|#|)
(defconst tokqt_sym '|"|)
(defconst cons_sym '|::|); 
(defconst escape_sym '|\\|)
(defconst neg_sym '|~|)
(defconst arrow_sym '|->|)
(defconst prod_sym '|*|)
(defconst list_sym '|list|)  
(defconst singlebar_sym '|\||) 
(defconst handle_sym (concat singlebar_sym singlebar_sym))
(defconst null_sym '|unit|)
(defconst cnr_sym '|`|)
(defconst mul_sym '|*|)
(defconst neq_sym '|<>|)
(defconst eq_sym '|=|)
(defconst wildcard_sym '|_|)
(defconst wildrecord_sym '|...|)
(defconst match_sym '|=>|)
(defconst  trap_sym '|?|)
(defconst lrecord_sym '|{|)
(defconst rrecord_sym '|}|)
(defconst space_sym '| |)
(defconst cr_sym (ascii 13)) ;carriage return
(defconst lf_sym (ascii 10)) ;line feed
(defconst tab_sym (ascii 9)) ;tab
(defconst lparen_sym '|(|)
(defconst rparen_sym '|)|)
(defconst lbrkt_sym '|[|)
(defconst rbrkt_sym '|]|)
(defconst period_sym '|.|)
(defconst comma_sym '|,|)
(defconst prime_sym '|'|)
(defconst colon_sym '|:|)
(defconst scolon_sym '|;|)
(defconst assign_sym '|:=|)
(defconst con_str_sym '|o|)


;***************************************************************************
;	CODE PROPERTY FOR RESERVED WORDS AND SYMBOLS
;***************************************************************************

(setq lang1 'ml1);
(setq lang2 'ml2);
(setq atom_rtn '(mlatomr));

;functions for defining property values:
(de unop (op code)		;unary operators and res. words.
    (putprop op code lang1)
);end unop

(de bnop (op code)		;binary operators and res. words.
    (putprop op code lang2)
);end bnop			

(de binop (op lp code)
  (putprop op code lang2) (putprop op lp prec_lev)
);end binop	

;***************************************************************************
;declarations
(unop '|val| '(dec_rtn nil))
(unop '|fun| '(dec_rtn nil))
(unop '|type| '(dec_rtn nil))
(unop '|datatype| '(dec_rtn nil))
(unop '|type| '(dec_rtn nil))
(unop '|abstype| '(dec_rtn nil))
(unop '|exception| '(dec_rtn nil))
(unop '|local| '(dec_rtn nil))

;other reserved words
(unop '|op| '(op_rtn))
(bnop '|as| '(as_rtn))
(unop '|nonfix| '(dec_rtn nil))
(unop '|infix| '(dec_rtn nil));left ass.
(unop '|infixr| '(dec_rtn nil));right ass.
(unop '|if| '(if_rtn))
(unop '|let| '(pre_let_rtn))
(bnop '|andalso| '(andalso_rtn))
(bnop '|orelse| '(orelse_rtn))
(unop '|case| '(case_rtn))
(unop '|fn| '(fn_rtn 310)) 
(bnop '|handle| '(handle_rtn))
(unop '|raise| '(raise_rtn))
(unop '|while| '(while_rtn))

;symbols
(unop lparen_sym '(tuple_rtn))
(unop lrecord_sym '(record_rtn))
(unop lbrkt_sym '(list_rtn))
(unop tml_sym '(parse_failed '|terminal symbol in the wrong place|))
(bnop colon_sym '(type_constraint_rtn))

;******************************************************************************
(defconst res_words `(|abstype| |and| |andalso| |as| |case| |datatype|
	|do| |data| |else| |end| |exception| |fn| |handle| |fun|
	|if| |in| |infix| |infixr| |let| |local| |nonfix| |of|
	|op| |orelse| |raise| |then| |type| |val| |with| |fun|
	|while| ,lparen_sym ,rparen_sym ,lbrkt_sym ,rbrkt_sym ,comma_sym
	,colon_sym ,scolon_sym ,singlebar_sym ,handle_sym 
	,match_sym ,trap_sym ))

(defconst dec_words '(|abstype| |exception| |local| |type| |val| |datatype|
		      |infix| |infixr| |nonfix| |fun|))

(defconst dec_markers '(mk-val mk-fun mk-datatype mk-abstype
		        mk-exception mk-local mk-infix mk-infixr
			mk-nonfix mk-decseq))



;************************************************************************
;define precedence for symbols and reserwed words

(defconst prec_lev 'mllp); set for the following definitions

;function for defining prec_level property.
(de def_prec (sym lev)
	(putprop sym lev prec_lev)
);end def_prec

(def_prec tml_sym 0)
(def_prec rparen_sym 10)
(def_prec rrecord_sym 10)
(def_prec rbrkt_sym 10)
(def_prec '|in| 20)
(def_prec '|end| 20)
(def_prec comma_sym 20)
(def_prec singlebar_sym 20)
(def_prec '|local| 35)
(def_prec '|exception| 35)
(def_prec '|abstype| 35)
(def_prec '|type| 35)
(def_prec '|datatype| 35)
(def_prec '|fun| 35)
(def_prec '|val| 35)
(def_prec '|nonfix| 35)
(def_prec '|infixr| 35)
(def_prec '|infix| 35)
(def_prec '|of| 40)
(def_prec '|do| 40)
(def_prec '|else| 40)
(def_prec '|then| 40)
(def_prec '|with| 40)
(def_prec match_sym 50)
(def_prec '|data| 60)
(def_prec '|as| 80)
(def_prec '|and| 80)
(def_prec trap_sym 200)
(def_prec handle_sym 270)
(def_prec '|fn| 300)
(def_prec '|case| 320)
(def_prec '|let| 340)
(def_prec '|while| 360)
(def_prec '|if| 380)
(def_prec '|raise| 400)
(def_prec '|handle| 415)
(def_prec '|orelse| 420)
(def_prec '|andalso| 440)
(def_prec colon_sym 530)
(def_prec '|op| 570)
;***************************************************************************
; set up token escape codes

(putprop '|n| (list lf) 'stringmacro)
(putprop '|t| (list tab) 'stringmacro)
(putprop '|"| (list tokqt) 'stringmacro)
(putprop '\\ (list escape) 'stringmacro);

;***************************************************************************
; LCF Stuff
(defconst cnr_rtn '|`|)
(defconst endcnr_sym '|`|)
(defconst anticnr_sym '|\^|)

(unop cnr_sym '(cnr-rtn))

; parse object language 
(de cnr-rtn ()
   (when (numberp token) (setq token (imploden (exploden token))))
   (prog1
      (selectq token
	   (|:| (gnt) `(mk-tyquot ,(olt)))
	   (t `(mk-quot ,(parse-ol)))
      );end selectq
      (ifn (eq token endcnr_sym)
	   (parse_failed '|OL: cannot find end of quotation|)
	   (gnt)
      );end ifn
   );end prog1
);end cnr_rtn

;***************************************************************************
;*	ML_JUXT 	       
;***************************************************************************
(de ml_juxt (x)
	(list 'mk-appn x (parse 790))
);end ml_juxt

;***************************************************************************
;*	MLATOMR 	       
;***************************************************************************
;*
;*DESCRIPTION: 
;*	       returns:
;*			real number : (mk-realconst ptoken)
;*		        integer     : (mk-intconst ptoken)
;*			string	    : (mk-stringconst ptoken)
;*			bool	    : (mk-boolconst ptoken)
;*			<op> var    : (mk-<op>var ptoken)
;*			wildcard    : (mk-wildcard)
;*			<op> con    : (mk-<op>con ptoken)    nullary -
;*	                <op> const  : (mk-<op>const ptoken) - nullary -
;*CALLED BY: parse
;*
;***************************************************************************

(de mlatomr ()
    (cond 
	  ((is_type_var ptoken); type variable cannot be var or con
	     	(parse_failed (concat '|identifier: | ptoken
		 '| cannot be a variable or a constructor|)))
	  ((or (memq ptoken res_words) ;a reserved word cannot be rebound!
		(memq ptoken tycons))
	       (parse_failed (concat '|identifier: | ptoken '| cannot be an identifier|)))
	  ((numberp ptoken) ;check if real or int
                (if (get (concat 'real ptoken) 'real); set in rtn: numb
	           (list 'mk-realconst (float ptoken))
	           (list 'mk-intconst ptoken)
	        );end if
          );end numberp
	  ((is-stringconst ptoken) (list 'mk-stringconst (cdr ptoken)))
	  ((eq ptoken wildcard_sym) '(mk-wildcard))
          ((or
	     (and 
		(eq lang1 'ml1);meta language
		(memq period_sym (explode ptoken))); "." cannot appear in sml id
	     (memq sharp_sym (explode ptoken))) ; "#" cannot appear in id
		(parse_failed (concat '|identifier: | ptoken
		   '| cannot be an identifier|)))
	  ((eq ptoken `true) `(mk-boolconst t)); boolean
	  ((eq ptoken `false) `(mk-boolconst nil)); boolean
	  (t 
	     (prog (ptok arity inf)
		;check if infix id is preceded by op (see op_rtn)
               (if (and (setq inf (is_infix ptoken)) no_op)
		   (parse_failed (concat '|identifier: | ptoken
                    '| is declared infix and must be preceded by "op"|)) 
	       );end if
	       (setq no_op t); reset no_op flg
	       (return
			(cond
			   ((setq arity (cdr (is_cons ptoken))); constructor ?
			      (if (eq arity 0); nullary!
				(if inf
				   `(mk-opconst ,ptoken)
				   `(mk-const ,ptoken)
				);end if
					     ;non-nullary!
				(if inf; indicate if id was prec. by op!
				   `(mk-opcon ,ptoken)
				   `(mk-con ,ptoken)
				);end if
			      ));end if
			   (t ;variable
				(if inf
				   `(mk-opvar ,ptoken)
				   `(mk-var ,ptoken)
				);end if
			   ));end t
	      );end return
	     );end prog
          );end t
	);end cond
);end mlatomr

;***************************************************************************
;*      IS-STRINGCONST
;***************************************************************************
(defun is-stringconst (tok)
  (and (consp tok) (eq (car tok) 'string)))

;***************************************************************************
;* 	SPACEP        
;***************************************************************************
;predicate
(de spacep (ch)
    (memq ch (list space cr lf tab))
);end spacep	

;***************************************************************************
;*	INITLEAN        
;***************************************************************************

(de initlean ()
    (setq token nil)
    (setq tokchs nil)
    (setq toktyp nil)
    (setq char space)
);end initlean


;***************************************************************************
;*	GNT
;***************************************************************************
;*
;*DESCRIPTION: get next token but skip comments.
;*
;***************************************************************************
(defun gnt ()
    (setq ptoken token)
    (setq ptoktyp toktyp)
    (gnt1)
    (while (eq token lcmnt_sym) ; if comment skip text
	   (skip_cmnt))
    token
)				; gnt

;*****************************************************************************
;*	SKIP_CMNT
;*****************************************************************************
(de skip_cmnt ()
    (let ((%notcmnt nil));indicate that we are in comment
	 (gnt1)
	 (while (not (eq token rcmnt_sym)); eof would cause a throw
		(cond ((eq token lcmnt_sym); nested comment
		       (skip_cmnt))
		      (t (gnt1)));still in comment , continue skipping
     ))
    (gnt1)			; return next symbol
);end skip_cmnt

;***************************************************************************
;*	GNT1
;***************************************************************************
;*
;*DESCRIPTION: Get next token from input.
;*
;*CALLED BY: gnt, skip_cmnt.
;*
;***************************************************************************
(de gnt1 ()
    (setq pchar char)
    (while (spacep char)(setq pchar (setq char (nextcn))))	;remove spacing
    (setq toktyp 1)
    (cond 
	 ((or (letterp char); alpha numeric id!
	      (eq char prime)); can start with letter or prime!
	 	(setq tokchs `(,char)); save first char.
		(alpha_ident))
	  ((eq char mulchr); - right comment symbol -
		(setq tokchs (list char))
		(cond
		   ((eq rparen (setq char (nextcn)))
			(newl tokchs char)
			(setq token (implode (reverse tokchs)))
			(setq char (nextcn)))
		   (t (sym_ident))));not a comment symb.
	 ((memq (ascii char) id_syms); symbolic id!
		(setq tokchs `(,char))
		(setq pchar char)
		(setq char (nextcn))
		(sym_ident))
	  ((digitp char); -number- 
		(setq tokchs (list char))	
	   	(if (eq lang1 'ml1) (numb) (alpha_ident)))
	  ((eq char sharp_chr); - numeric label -
		(setq tokchs (list (setq char (nextcn))))
		(cond
		   ((eq lang1 'ol1);object lang.
			(setq toktyp 2)
			(setq token sharp_sym))
		    ((and (not (digitp char)) %notcmnt)
		      (parse_failed (concat '|record: | 
			(if (spacep char) '|<space>| (ascii char))
		     '| found in numeric label|)))
		    (t (setq token (concat sharp_sym (int))))
		));end cond
	  ((eq char tokqt)          ; -string- 
		(setq tokchs nil); skip tokqt	
	   	(tcn)); get the rest of string
	  ((eq char period); - record wildcard -
		(setq tokchs (list char))
		(while (eq (setq char (nextcn)) period)
		   (newl tokchs char)
		);end while
		(setq toktyp 2)
		(setq token (implode (reverse tokchs)))
		(if (and (eq lang1 'ml1);meta language and
		         (not (eq (length tokchs) 3)); token = .... 
			 %notcmnt);and not in comment
			(parse_failed (concat '|record: | token
		  `| cannot be an identifier|))
	        ));end ifn
	   ((eq char lparen)            ; - left comment symbol  ? -
		(setq tokchs (list char))
		(cond
; code below removed to allow comments in OL (2/2/87)
;		   ((eq lang1 'ol1); object lang
;			(setq token lparen_sym)
;			(setq char (nextcn)))
		   ((eq mulchr (setq char (nextcn))); comment symbol
			(newl tokchs char)
			(setq token (implode (reverse tokchs)))
			(setq char (nextcn)))
		   (t (setq token lparen_sym)
		      (cond ((spacep char)
			(while (spacep char)
			   (setq char (nextcn))
			);end while
			;check that next symbol is not ")" :
			(if (and (eq char rparen); (<space>) -> error
				 %notcmnt);end and
			  (parse_failed 
			    '|tuple: space not allowed in 0-tuple|)))
		       ));end cond
		));end cond
	  (t (setq toktyp 2)(setq token (ascii char)) (setq char (nextcn)))
     );end cond
     token ;return token
);end gnt1


;***************************************************************************
;*	NUMB        
;***************************************************************************
;*DESCRIPTION: returns the value of a number (real/integer)
;*	       the real prop. of token is set to t if it is a real num.
;*
;***************************************************************************
(de numb () 
    (prog (real) 
	(setq token (nu))
	(cond (%real; real number flag=t ?
	   (putprop (concat 'real token) 't 'real)
	   (setq %real nil))
	);end cond
	(return token)
    );end prog
);end numb

;***************************************************************************
;*	NU        
;***************************************************************************
;*
;*DESCRIPTION: Checks if the number is a real number or an integer and 
;*	       returns the value of it.       
;*
;*CALLED BY: numb
;*
;*LOCAL VARIABLES: num : value of number.
;*
;***************************************************************************
(de nu ()
     (prog (num) (setq num (int)) 
          (if (eq char period)
		(setq num (plus num (fraction))); real number
	  );end if
		(cond
			((or (eq char #/e) (eq char #/E)); Exponent
			    (setq char (nextcn)); skip e/E
			    (setq %real t);indicate real number
			    (return 
			      (times num 
				(expt 10 
				   (cond
					((eq char neg_tok); negative exponent
					   (setq char (nextcn))
					   (minus (int)))
					(t (int))
				   );end cond
				);end expt
			      );end times
			    ));end return 
			(t 
			    (return num))) ;integer
		);end cond
      );end prog
;end nu

;***************************************************************************
;*	VALUE        
;***************************************************************************
;returns the numerical value of a character.

(de value (ch)
	(- ch #/0))
;end value

;***************************************************************************
;*	INT        
;***************************************************************************
;returns the value of an integer.

(de int ()
   (if (and (not (digitp char)) %notcmnt)
      (parse_failed (concat '|number: | (if (spacep char) '|<space>| (ascii char))
	'| found where a digit was expected|))
   );end ifn
   (prog (accu) 
		(setq accu (value char))
		(while (digitp (setq char (nextcn)))
		  (setq accu (+ (* accu 10) (value char))))
		(return accu))
   );end prog
;end int

;***************************************************************************
;*	FRACTION        
;***************************************************************************
;returns the value of the fraction part of a real number. 

(de fraction ()
    (if (and (not (digitp (setq char (nextcn)))) %notcmnt) ; next character digit?
      (parse_failed (concat '|number: | (if (spacep char) '|<space>| (ascii char))
	'| found where a digit was expected|))
    );end ifn
    (prog (frac mul) 
	(setq frac (times (setq mul 0.1) (value char)))
        (while (digitp (setq char (nextcn)))
             (setq frac 
		(plus frac (times (value char) (setq mul (quotient mul 10)))))
	);end while
        (setq %real t) ;indicate that number is real number
        (return frac)
    );end prog
); end fraction

;***************************************************************************
;*	SYM_IDENT        
;***************************************************************************
;*
;*DESCRIPTION: Returns the name of a symbolic identifier. 
;*
;*CALLED BY: gnt
;*
;***************************************************************************
(de sym_ident ()
	(setq toktyp 2)
	(while (memq (ascii char) id_syms) ;char valid id-sym?
	    (newl tokchs char)
	    (setq pchar char)
	    (setq char (nextcn))
        );end while 
	(cond; gnt1 cannot cope with: (*comment!*) ;(!* is sym. iden.)
		;we have to identify rcmnt_sym on char level!
	  ((and (not %notcmnt);we are in comment
		(eq pchar mulchr);and last token is comment bracket
		(eq char rparen))
		   (setq char (nextcn))
	           (setq token rcmnt_sym))
	   (t (setq token (implode (reverse tokchs))))
	);end cond
);end sym_ident

;***************************************************************************
;*	ALPHA_IDENT        
;***************************************************************************
;*
;*DESCRIPTION: Returns the name of an alphanumeric identifier. 
;*
;*CALLING: alphanump
;*
;*CALLED BY: gnt
;*
;***************************************************************************
(de alpha_ident ()
	(while (alphanump (setq char (nextcn)))
		(newl tokchs char)
	);end while
	(setq token (implode (reverse tokchs)))
);end alpha_ident

;***************************************************************************
;*	TCN
;***************************************************************************
;*
;*DESCRIPTION: Returns a string constant. It handles the following escape
;*	       sequences:
;*			   \n     : end-of-line.
;*			   \t     : tab.
;*			   \ddd   : single character with ascii code ddd.
;*			   \\     :\
;*			   \f..f\ : this sequence is ignored.
;*			   \^c    : control character c.
;*			   \"     : "
;*
;*CALLED BY: gnt
;*
;***************************************************************************

(de tcn ()
     (while (neq (setq char (nextcn)) tokqt)
	 (if (and (eq char escape) %notcmnt); escape sequence
	;test for %notcmnt to avoid lock in cmnt: (* comment "abc\" *)
	     (setq tokchs (nconc (escape_rtn (nextcn)) tokchs))
	     (newl tokchs char)
	 );end if
     );end while
     (setq char (nextcn))
     (setq token (cons 'string (implode (reverse tokchs))))
);end tcn

;***************************************************************************
;*	ESCAPE_RTN        
;***************************************************************************
;Takes care of escape sequences within a string. See 'tcn'.

(de escape_rtn (char)
   (cond
	((digitp char) ; octal ascii code
	   (list (asc)))
	((selectq char
	   (#/n (list lf))
	   (#/t (list tab))
	   (#/" (list tokqt))
	   (#/\ (list escape))))
	((eq char uparrow)		      ; (* "mmm\"  *)
	   (setq char (nextcn))
	   (list (control_char)))
	((spacep char) (while (spacep (setq char (nextcn))))
	        (if (and (not (eq char #/\)) %notcmnt)
			(parse_failed '|string: missing "\\" in escape sequence|)))
	(t (if %notcmnt (parse_failed '|string: incorrect escape sequence |))))
);end escape-rtn

;***************************************************************************
;*	ASC        
;***************************************************************************
(de asc () (+ (* 100 (value char)) (* 10 (next_dig)) (next_dig)))

;*****************************************************************************
;*	CONTROL_CHAR
;*****************************************************************************
(de control_char ()
   (cond 
	((bounded #/a char #/z)
	   (- char 96))
	((bounded #/A char #/Z)
	   (- char 64))
	(t 
	 (if %notcmnt 
	   (parse_failed `|string: funny control character in escape sequence|)))
   );end cond
);end control_char

;*****************************************************************************
;*	NEXT_DIG
;*****************************************************************************
;get next digit in ascii-code
(de next_dig ()
	(if (and %notcmnt (not (digitp (setq char (nextcn)))))
	   (parse_failed `|string: non-digit in ascii-code|)
	   (value char)
	);end ifn
);end next_dig

;***************************************************************************
;*
;*	FUNCTIONS
;*
;***************************************************************************

;*****************************************************************************
;*	DEC_TEST1	
;*****************************************************************************
;test for declaration, used when expression is expected
(de dec_test1 (exp_typ)
   (if (memq token dec_words)
	(parse_failed  (concat exp_typ  token
	   '|-declaration found where expression was expected|)
	);end parse_failed
   );end if
);end dec_test1

;*****************************************************************************
;*	DEC_TEST2
;*****************************************************************************
;same as above but used when exp/pat is expected.
(de dec_test2 (exp_typ)
	     (if (memq token dec_words)
		(parse_failed  (concat exp_typ token
   '|-declaration found where expression or pattern was expected|)
		);end parse_failed
	     );end if
);end dec_test2

;*****************************************************************************
;*	LOC_ON
;*****************************************************************************
;Indicate that we are parsing a local dec. Tested in dec_rtn.
(de loc_on ()
   (def_prec tml_sym 35); ";" is dec-delimiter in locals and lets
   (setq %loc_flg t)
);end loc_on

;*****************************************************************************
;*	lOC_OFF
;*****************************************************************************
(de loc_off (x)
   (def_prec tml_sym 0); back to terminator
   (setq %loc_flg nil)
   x; return x
);end loc_off

;*****************************************************************************
;*	TOP_INF
;*****************************************************************************
;returns the top most id on %inf_stack
(de top_inf ()
	(ifn (null %inf_stack) 
	    (car %inf_stack))
);end top_inf

;*****************************************************************************
;*	POP_INF
;*****************************************************************************
;pop an infix id. from %inf_stack
(de pop_inf ()
	(setq %inf_stack (cdr %inf_stack))
);end pop_inf

;*****************************************************************************
;*	PUSH_INF
;*****************************************************************************
;push an infix id on %inf_stack.
(de push_inf (tok)
	(setq %inf_stack (cons token %inf_stack))
);end 

;*****************************************************************************
;*	GET_INFASS
;*****************************************************************************
;association for infixed identifiers.
;returns l : tok left ass.
;	 r : tok is right ass.
;tok is a user def. infixed id.
(de get_infass (tok)
	(car (is_infix tok))
);end get_infass

;*****************************************************************************
;*	GET_INFCODE
;*****************************************************************************
;return code for binary op or infixed identifiers.
(de get_infcode (tok)
    (if (and (eq lang1 'ml1) (is_infix tok))
     '(inf_appl_rtn inf_lev)
      (get tok lang2)
    );end if
);end get_infcode

;*****************************************************************************
;*
;*****************************************************************************
;get id's infix prec. level
(de get_infprec (id)
	(cdr (is_infix id))
);end get_infprec


;*****************************************************************************
;*	IS_INFIX
;*****************************************************************************
;returns t if id is infix.
;t=layer on %inf where id is found,or id's "mlinfix"  prop. if top level
;({l/r} . prec_lev)
(de is_infix (id)
   (prog (x)
        (setq x (is_infix2 id %inf))
        (return
		(if (eq x 'nonf);nonfixed id
		    nil ;return nil
		    (or x (get id 'mlinfix))
		);end if
	);end return
   );end prog
);end is_infix

;*****************************************************************************
;*	IS_INFIX2
;*****************************************************************************
;returns t if id occurs in %inf.
(de is_infix2 (id l)
   (cond
	((null l) nil)
	((memq id (caar l))
	   (if (eq (cadar l) 'nonfix)
		'nonf ;
		(cddar l); return ({l/r} . prec_lev)
	   ));end if
	(t (is_infix2 id (cdr l)))
   );end cond
);end is_infix2

;*****************************************************************************
;*	TYCON_CHECK
;*****************************************************************************
;check for attempts to rebind predeclared tycons
(de tycon_check (tycon dec_typ)
   (if (or (memq tycon tycons) (eq tycon 'ref) (eq tycon 'real))
	(parse_failed (concat dec_typ tycon
	   '| cannot be redeclared as type constructor|)
	);end parse_failed
   );end if
);end tycon_check

;*****************************************************************************
;*	GET_GLOBPREC
;*****************************************************************************
;get global precedence for tok.
(de get_globprec (tok)
  (or (get tok prec_lev)
      (if (and (eq lang1 'ml1) (is_infix tok)) inf_lev))
);end get_globprec


;******************************************************************************
;predicates:

(de upperp (ch)
    (bounded #/A ch #/Z)
);end upperp

(de lowerp (ch)
    (bounded #/a ch #/z)
);end lowerp

(de letterp (ch)
    (or (upperp ch) (lowerp ch))
);end letterp

(de digitp (ch)
    (bounded #/0 ch #/9)
);end digitp


(de alphanump (ch)
    (or (upperp ch)
	(lowerp ch)
	(digitp ch)
	(eq ch #/')
	(eq ch #/_))
);end alphanump

;*****************************************************************************
;*	PARSE_FAILED
;*****************************************************************************
;print error message and exit to top level loop
(de parse_failed (msg); temp routine
    (llprinc msg)
    (llterpri)
    (llprinc '|skipping: |)
    (llprinc token)
    (llprinc space_sym)
    (do ((i %skiplimit (1- i)))
	((eq token tml_sym) (if (<= i 0) (llprinc '|. . .|)))
	(gnt)
	(when (> i 0) (llprinc token) (llprinc space_sym))
    );end do
    (initlean)
    (def_prec tml_sym 0);back to terminator (could have been changed!)
    (unop tml_sym '(parse_failed
			'|terminal symbol in the wrong place|))
    (def_prec eq_sym inf_lev)
    (def_prec colon_sym 530)
    (*exit parse 0)
);end parse_failed

;*****************************************************************************
;*	CHECK_EQ_SYM
;*****************************************************************************
(de check_eq_sym (msg)
    (unless (eq token eq_sym)
      (parse_failed  msg))
    (gnt)
);end check_eq_sym

;*****************************************************************************
;*	IS_TYPE_VAR
;*****************************************************************************
;returns t if tok is type variable.
(de is_type_var (tok)
	(eq prime (car (exploden tok)))
);end is_type_var

;*****************************************************************************
;*	IS_NUMLABP
;*****************************************************************************
;returns t if tok is a numeric label
;only used in record rtn. before # is removed! 
(de is_numlabp (tok)
  (eq sharp_chr (car (exploden tok)))
);end is_numlabp

;*****************************************************************************
;*	SPLICE
;*****************************************************************************
;remove the part of env that has been added in a local dec. or let exp.
(de splice (env s1 s2)
   (cond
	((equal env s2) s1)
	(t (cons (car env) (splice (cdr env) s1 s2)))
   );end cond
);end splice

;***************************************************************************
;*	UPDATE_INF
;***************************************************************************
;update infixes, give ids on %inf infix property (mlinfix) if infix
;and remove infix property if nonfix.
;called in tmlloop (see S-tml)
(de update_inf ()
   (setq %inf (reverse %inf))
   (while %inf
	(if (eq (cadar %inf) 'infix)
	  (eval-remember
	   `(mapc
		;give id infix property
		'(lambda (x) (putprop x ',(cddar %inf) 'mlinfix)
			     (def_prec x ,inf_lev))
	         ',(caar %inf)
	   );end mapc
	 );end eval..
	(eval-remember
	   `(mapc
		;remove infix property
	 	'(lambda (x) (remprop x 'mlinfix)
			     (remprop x prec_lev))
	         ',(caar %inf)
	   );end mapc
	);end eval..
	);end if
	(setq %inf (cdr %inf))
   );end while
);end update_inf


;***************************************************************************
;*       IS_CONS 
;***************************************************************************
;DESCRIPTION: Returns t if con has previously been declared as constructor
; in a datatype declaration. If it is a top level constructor, then it has
; a lisp property (constr_info) to indicate its constructor status. 
; Otherwise, check for the occurrence of it in the the global list %constr 
; format :
; ( .. (tycon list_of_new_constr list_of_old_constr) ..) }. If con occurs
; in a list list_of_new_constr, then it is a constructor. If it occurs in
; a list list_of_old_constr, then it is a variable iff it doesn`t occur in
; a list_of_new_constr with a type constructor other than the type constructor
; it was most recently declared with (ie tycon in the layer currently being
; checked).
; t= (tycon . arity).

(de is_cons (con)
  (prog (x)
	(setq x (is_cons1 con %constr nil));defined in this sequence?
	(return
	   (if (eq x 'hid); hidden constructor
		nil; ie. variable !
		(or x (get con 'constr_info))
	   );end if
	);end return
   );end prog
);end is_cons

;*****************************************************************************
;*	IS_CONS1
;*****************************************************************************
;returns: t if con occurs in a list_of_new_constr
;         nil if it can`t be found.
;	  calls is_cons2 if con occurs in a list_of_old_constr
(de is_cons1 (con l tycon_l)
   (prog (x)
	(return
	  (cond
		((null l) nil)
		((setq x (cdr (assoc con (cadar l))));list_of_new_constr
		   `(,(caar l) . ,x)); (tycon . arity)
		((assoc con (caddar l)) ;list_of_old_constr
		   (is_cons2 con (cdr l) (cons (caar l) tycon_l))); 
		(t (is_cons1 con (cdr l) (cons (caar l) tycon_l)))
	   );end cond
	);end return
   );end prog
);end is_cons1

;*****************************************************************************
;*	IS_CONS2
;*****************************************************************************
;returns: `hid if con does not occur in any list_of_new_constr in the tail of %constr
;	   t if it occurs in some tycon`s list_of_new_constr.
;	   (ie. it was not hidden after all!)
(de is_cons2 (con l tycon_l)
  (prog (x)
    (return
      (cond
	((null l) 'hid);identifier is hidden constr. !
	((memq (caar l) tycon_l);tycon`s constr. have been checked prev.
	   (is_cons2 con (cdr l) tycon_l))
	((setq x (cdr (assoc con (cadar l)))); list_of_new_constr
	   `(,(caar l) . ,x));id. is contructor after all!
	(t (is_cons2 con (cdr l) (cons (caar l) tycon_l)))
      );end cond
    );end return
  );end prog
);end is_cons2

;***************************************************************************
;*	UPDATE_CONS
;***************************************************************************
;*DESCRIPTION: Give constructors in %constr "constr_info" property (format:
;* (tycon . arity)) and type constructors "constr" property (list of constructors).
;* Once a tycon and its constructors have been updated, each new occurrence
;* of it in %constr is ignored.
;*
;***************************************************************************
(de update_cons ()
  (prog (tycon_l con_l)
   (while %constr
     (cond ((not (memq (caar %constr) tycon_l));
	(setq tycon_l (cons (caar %constr) tycon_l))
	(eval-remember
	   `(putprop ',(caar %constr) ',(cadar %constr) 'constr);new property
	);end eval...
	;remove property for old constructors:
	(mapc
	  '(lambda (x) 
    	     (ifn (memq (car x) con_l)
	      (eval-remember
		`(remprop ',(car x) 'constr_info)
	       );end eval-remem.
	     ));end lambda
	    (caddar %constr)
	);end mapc
	;new constructors:
	(mapc
	   '(lambda (x) 
	      (eval-remember
		`(putprop ',(car x) '(,(caar %constr) . ,(cdr x)) 'constr_info)
	       );end eval..
		(setq con_l (cons (car x) con_l))
	   );end lambda
	   (cadar %constr)
	  ));end mapc
      );end cond
      (setq %constr (cdr %constr))
   );end while
  );end prog
);end update_cons

;***************************************************************************
;* 	OK_CONS
;***************************************************************************
;returns t: if con is not a constructor or if it's a constr. with a tycon in tycon_l.
;      nil: otherwise
(de ok_cons (con tycon_l)
   (prog (x)
	(setq x (is_cons con))
	(cond
	   ((memq (car x) tycon_l);con is cons. with type constr. in tycon_l. ok!
		(return t))
	   (x (return nil));con is cons with type const other than tycon
	   (t (return t));con is not cons. ok!
	);end cond
    );end prog
);end ok_cons


;***************************************************************************
;*	ADD_CONLAY
;***************************************************************************
;*
;*DESCRIPTION: Add a new layer of constructors to %conlay and check for
;* multible occurrence of constructor. Check also that a constructor
;* (if prev. declared as such) may be rebounded to another type constructor.
;*
;***************************************************************************
(de add_conlay (conlay)
 (prog (tycon_l con_l)
;build up a list of type constr. and value constr.
;and check for multible occurrences of constr.
   (mapc
	`(lambda (x) (setq tycon_l (cons (car x) tycon_l))
		     (mapc  
		        '(lambda (y) 
			    (ifn (member y con_l)
				(setq con_l (cons y con_l))
				
			        (parse_failed 
				  (concat
	  '|datatype declaration: multiple occurrence of identifier - |
				  (car y)))
		            );end ifn
			  );end lambda
			  (cdr x)
		       );end mapc
	 );end lambda
	 conlay
   );end mapc
   ;check that each constructor in conlay may be rebound.
   (mapc
	`(lambda (x) 
	   (ifn 
	     (ok_cons (car x) tycon_l);decl as constr.
				;with tycon other than those in tycon_l?
	      (parse_failed (concat '|datatype declaration: | (car x)
		'| is already defined as constructor|))
	));end ifn
	con_l
   );end mapc
   ;add new layers to %constr
   (while conlay
     (newl %constr
	`(,(caar conlay) ,(cdar conlay)
		,(append (most_recent_cons (caar conlay)) 
			 (old_cons (car conlay))))
      );end newl
      (setq conlay (cdr conlay))
    );end while
 );end prog
);end add_conlay

;*****************************************************************************
;*	MOST_RECENT_CONS
;*****************************************************************************
;returns constructors most recently declared with tycon.
(de most_recent_cons (tycon)
   (or (cadr (assoc tycon %constr)) (get tycon 'constr))
);end most_recent_cons

;*****************************************************************************
;*	OLD_CONS
;*****************************************************************************
;all old constructors (including those which still are constructors)
(de old_cons (tycon)
   (caddr (assoc tycon %constr ))
);end old_cons


;***************************************************************************
;*	OP_RTN
;***************************************************************************
;*
;*DESCRIPTION: Evaluated if ptoken is "op". A global flag no_op is set to nil.
;*	       no_op is checked in mlatomr and parse.
;*
;***************************************************************************
(de op_rtn ()
	(if (is_type_var token)
	    (parse_failed 
		(concat '|identifier: "op" cannot precede a type variable  op |
		token))
	);end ifn
	(ifn (is_infix token)
	    (parse_failed 
	      (concat '|identifier: "op" can only precede an infixed identifier   op |
		   token))
	);end ifn
	(setq no_op nil)
	(gnt)
	(setq par_res (eval atom_rtn)); next item is an id. 
);end op_rtn

;***************************************************************************
;*	TYPE_CONSTRAINT_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a type constraint. Returns: (mk-straint EXP TY)
;*
;***************************************************************************

(de type_constraint_rtn ()
	(list 'mk-straint par_res (type_exp_rtn))
);end type_constraint_rtn

;***************************************************************************
;*
;*	EXPRESSIONS/PATTERNS
;*
;
;***************************************************************************
;*	INF_APPL_RTN
;***************************************************************************
;*
;*DESCRIPTION: Inf_appl_rtn is evaluated should ptoken be a variable or
;*	       a constructor with user defined infix property.
;*	       If ptoken is declared as a constructor then 
;*		(mk-infappn (mk-con op) (mk-tuple EXP1 EXP2))
;*		is returned. If ptoken is a variable then the same result as
;*		above is returned but with mk-con replaced by
;*		mk-var.
;*
;*CALLING: is_cons
;*
;*
;***************************************************************************
(de inf_appl_rtn (parse_lev)
	(let ((lhs par_res)(op ptoken));save lhs of exp. or pattern
		(parse parse_lev);parse rhs.
	   	`(mk-infappn 
		   ,(if (is_cons op)
			`(mk-con ,op)
			`(mk-var ,op)
		    );end if
		    ,lhs ,par_res
		  );end mk-infappn
	);end let
);end appl_rtn

    
;***************************************************************************
;*	AS_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a layered pattern. Returns (mk-laypat PAT1 PAT)
;*	       where pat1=<op> var <:ty>
;*
;*LOCAL VARIABLES: lhs = var:ty.        
;*
;***************************************************************************

(de as_rtn ()
	(let ((lhs par_res))
	   (ifn
		(or
		   (memq (car lhs) '(mk-var mk-opvar))
		   (and (eq (car lhs) 'mk-straint)
			(memq (caadr lhs) '(mk-opvar mk-var)))
		);end or
		(parse_failed '|layered pattern: syntax error |)
	   );end ifn	
	  `(mk-laypat ,lhs ,(parse 70));right ass.
	);end let
);end as_rtn

;***************************************************************************
;*	EXPSEQ_RTN
;***************************************************************************
;*returns: (mk-expseq (EXP1 .. EXPn-1) EXPn)
;*
(de expseq_rtn ()
   (prog (res old)
	(setq old par_res)
	(while (eq token scolon_sym)
	   (gnt)
	   (dec_test1 '|expression sequence: |)
	   (newr res old)
	   (setq old (parse 35))
	);end while
	(return `(mk-expseq ,res ,old))
   );end prog
);end expseq_rtn


;***************************************************************************
;*	TUPLE_RTN
;***************************************************************************
;*
;*DESCRIPTION: Tuple_rtn is evaluated if token is a left paranthesis.
;*	       It returns the following:
;*
;*		   ()    -> (mk-empty)
;*		   (exp) -> EXP
;*		   (pat) -> PAT
;*		   (exp, .. ,exp) -> (mk-tuple EXP1 .. EXPn)
;*		   (exp1; .. ;expn) -> (mk-expseq EXP1 .. EXPn) (via expseq_rtn)
;*
;*LOCAL VARIABLES: res : result of tuple_rtn.
;*		   tuple_flg : indicates tuple.
;*
;*COMMENT:  parse is called with prec.lev 25 to enable type constraints
;*	   in a fun binding (eg. f(x:int)=x+1). prec_lev for ':' is changed
;*	   in fun_bind_rtn.
;*	   Since the last expression of a tuple is added to res on 
;*	   returning the result, a check cannot be made for the length of res
;*	   to determine if exp is a tuple or a paranth. exp. Hence, the flag
;*	   to indicate a tuple. 
;*
;***************************************************************************
(de tuple_rtn ()
   (prog (res tuple_flg seq save exp)
	(cond ((eq token rparen_sym)
	    (gnt)
	    (return '(mk-empty)))
	);end cond
	loop
	   (setq save (get tml_sym prec_lev))
	   (def_prec tml_sym 20);expr. delimiter
	   (unop tml_sym nil);enable sequence
	   (dec_test1 '|tuple: |);check for declarations
	   (setq exp (parse 25));parse exp or seq
	   (def_prec tml_sym save);back to previous
	   (unop tml_sym '(parse_failed ; back to terminal
			'|terminal symbol in the wrong place|))
	   (if (and
		(> (length res) 0); tuple !
	        (eq token tml_sym)); 
	     (parse_failed 
		'|tuple:  ";" cannot delimit an expression |)
	   );end if
	   (cond
	     ((eq token tml_sym);sequence
			(def_prec tml_sym 20);expression delimiter
		        (unop tml_sym nil)
			(setq res (expseq_rtn))
			(def_prec tml_sym save);back to prev. value
		        (unop tml_sym '(parse_failed
			      '|terminal symbol in the wrong place|))
			(ifn (eq token rparen_sym)
			   (parse_failed (concat  '|expression sequence: | token
			     '| found where right paranthesis was expected|)
			   );end parse_failed
			   (gnt)
			);end ifn
			(return res))
	   );end cond
	   (cond
		((eq token comma_sym)
		   (setq tuple_flg t); tuple!
		   (newr res exp)
		   (gnt)
		   (go loop))
		((eq token rparen_sym)
		   (gnt)
		   (return  
			(if tuple_flg
		           (cons 'mk-tuple
		             (newr res ;add last expr.
				exp
			     );end newr
			   );end cons
			   exp; simple exp. or pat.
			);end if
		    ));end return
		(t (parse_failed  (concat 
		     (if tuple_flg '|tuple: | '|pattern/expression: |)
			token 
		'| found where comma or right paranthesis was expected|)))
	   );end cond
   );end prog
);end tuple_rtn

;***************************************************************************
;*	Record_rtn
;***************************************************************************
;*
;*DESCRIPTION: Record_rtn is evaluated if token is a left curly bracket.
;*	       Returns:
;*
;*		   {}    -> (mk-record)
;*		   {lab1=exp .. labn=expn} -> 
;*				(mk-record lab1.EXP1 .. labn.EXPn)
;*		   
;*		   similar for patterns with the addition:.
;*			wild record -> (mk-wildrecord lab1.PAT1 .. labn.PATn)
;*			
;*LOCAL VARIABLES: res : result of tuple_rtn.
;*		   label : user def. label.
;*		   num_flg : set to t if first label is numeric.
;*			 x : (mk-infappn (mk-var =) ... -> lab={exp/pat}
;*			     (mk-laypat ... -> id<:ty> as pat (label=id)
;*
;*COMMENT: parse is called with prec.lev 25 to enable type constraints
;*	   in fun bind.(eg. f{#1=x:int}=x+1). prec_lev for ':' is changed
;*	   in fun_bind_rtn.
;*	   Each element in the record is parsed by calling the general 
;*	   parsing routine. In the case of a numeric label, only the
;*	   exp/pat is parsed since #d would cause a parse error.
;*	   Result of parsing an element and the interpretation:
;:	   (mk-infappn (mk-var =) ID {EXP/PAT} -> id={pat/exp}
;*	   (mk-infappn (mk-var x) ... ) where x <> "=" -> error.
;*	   (mk-laypat ... ) -> layered pattern.
;*
;***************************************************************************

(de record_rtn ()
   (prog (res label num_flg x lab_l)
	(cond
	  ((eq token rrecord_sym);empty record
	   (gnt)
	   (return '(mk-record)))
	);end cond
	(if (is_type_var token)
	   (parse_failed (concat '|record: |
		'|funny label - | token))
	);end if
	(if (is_numlabp token);numeric label ?
	   (setq num_flg t))
loop
	(cond
	   ((eq token wildrecord_sym);wild record
		(gnt)
		(ifn (eq token rrecord_sym); must be at end of record
		  (parse_failed  
		    '|record: "..." in the wrong place "|
		   );
		);end ifn
	        (gnt)
		(return (cons 'mk-wildrecord res))
	    )
	);end cond
	(if (memq token lab_l)
	   (parse_failed
		(concat
		'|record: multiple occurrence of label - |
		 token))
	);end if
	(setq lab_l (cons (setq label token) lab_l))
	(if num_flg;check for mixt. of numeric and alpha labels.
	   (if (not (is_numlabp label))
		(parse_failed 
		   (concat '|record: | label
		   '| found where a numeric label was expected|
		   ));end parse_failed
		(setq label (concatl (cddr (explode label))));pick out number
	   );end if
	   (if (is_numlabp label)
		(parse_failed
		   (concat '|record | label
		   '| found where an alphabetic label was expected|
		   ));end parse_failed
	   );end if
    	);end if
	(newr res (cons label
	 (cond 
	   ((is_numlabp token);special case since #d is not an identifier,
	     (gnt)        ;and would cause error in parsing as below!
	     (check_eq_sym '|record: missing "=" |)
	     (dec_test2 '|record: |); check for decl.
	     (parse 25))
	   (t   
	     (setq x (parse 25))
	     (cond
		((eq (car x) 'mk-infappn);  label={exp/pat} !!
		   (ifn (eq (cadadr x) eq_sym); missing "=" ?
			(parse_failed
			  '|record: missing "=" |)
		   );end ifn
		   (cadddr x));return pattern
		((eq (car x) 'mk-laypat); layered pattern !
		   x); return parse tree for as-pattern.
		(t (parse_failed '|record: syntax error |))
	     ));end cond
	 ));end cond
	);end newr
	(cond
	   ((eq token comma_sym)
		(gnt)
		(go loop))
	   ((eq token rrecord_sym)
		(gnt)
		(return (cons 'mk-record res)))
	   (t 
	      (parse_failed (concat '|record: | token
		'| found where comma or curly bracket was expected|)
              ))
  	);end cond
   );end prog
);end record_rtn

;***************************************************************************
;* 	LIST_RTN
;***************************************************************************
;*
;*DESCRIPTION: List_rtn is evaluated if token is a left bracket. It returns
;*	       the following:
;*		   [exp, .. ,exp] : (mk-list EXP .. EXP)
;*		   [pat, .. ,pat] : (mk-list PAT .. PAT)
;*
;*LOCAL VARIABLES: res : result of list_rtn.
;*
;***************************************************************************

(de list_rtn ()
	(prog (res) (setq res (list 'mk-list))
	   (cond ((eq token rbrkt_sym);empty list
		(gnt)
		(return res))
	   );end cond
	loop
	   (dec_test2 '|list: |);check for declarations
	   (newr res (parse 25)); parse expression or pattern
	   (cond
		((eq token comma_sym)
		   (gnt)
		   (go loop))
		((eq token rbrkt_sym)
		   (gnt)
		   (return res))
		(t (parse_failed  (concat '|list: |token 
		'| found where comma or right bracket was expected|)))
	   );end cond
	);end cond
);end list_rtn

;***************************************************************************
;*	AND_ALSO_RTN	
;***************************************************************************
;*
;*DESCRIPTION: Parse an andalso expression.
;*
;*RESULT: (mk-andalso EXP1 EXP2)
;*
;***************************************************************************
(de andalso_rtn ()
	(list 'mk-andalso par_res (parse 450) )
);end and_also_rtn


;***************************************************************************
;*	OR_ELSE_RTN	
;***************************************************************************
;*
;*DESCRIPTION: Parse an orelse expression.
;*
;*RESULT: (mk-orelse EXP1 EXP2)
;*
;***************************************************************************
(de orelse_rtn ()
	(list 'mk-orelse par_res  (parse 430))
);end orelse_rtn

;***************************************************************************
;*	RAISE_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a raise expression.
;*
;*RESULT: (mk-raise exn EXP)
;*
;***************************************************************************
(de raise_rtn ()
	(if (is_type_var token)
	   (parse_failed (concat '|raise expression: | token
	   '| is not a valid excpetion name|))
	);end if
	(prog (res) 
		(setq res (list 'mk-raise token)); token is exception name
		(gnt)
		(return
		   (cond
			((eq token '|with|)
			   (gnt)
			   (newr res (parse 410)));parse expression
			(t res)
		   );end cond
		);end return
	);end prog
);end raise_rtn


;***************************************************************************
;*	IF_RTN
;***************************************************************************
;*
;*DESCRIPTION:Parse an if expresson.
;*
;*RESULT: (mk-if EXP1 EXP2 EXP3)
;*
;***************************************************************************
(de if_rtn ()
	(prog (res)
	   (dec_test1 '|if expression: |)
	   (setq res (list 'mk-if (parse 50))); parse first exp.
	   (ifn (eq token '|then|) 
		(parse_failed '|if expression: missing "then" |))
	   (gnt)
	   (dec_test1 '|if expression: |)
	   (newr res (parse 50)); parse second exp.
	   (ifn (eq token '|else|) 
		(parse_failed '|if expression: missing "else" |))
	   (gnt)
	   (dec_test1 '|if expression: |)
	   (newr res (parse 390)); parse last exp.
	   (return res)
	);end prog
);end if_rtn

;***************************************************************************
;*	WHILE_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a while expression.
;*
;*RESULT: (mk-while EXP1 EXP2)
;*	
;***************************************************************************
(de while_rtn ()
	(prog (res)
	   (dec_test1 '|while expression: |)
	   (setq res (list 'mk-while (parse 50))); parse first exp.
	   (ifn (eq token '|do|)
		(parse_failed '|while expression: missing "do" |))
	   (gnt)
	   (dec_test1 '|while expression: |)
	   (newr res (parse 370)); parse second exp.
	   (return res)
	);end prog
);end while_rtn

;***************************************************************************
;*	PRE_LET_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Saves the value of the constructor list %constr and the infix
;*	       list %inf. Since both infixes and constructors posses
;*	       scope, %constr and %inf get back their old values after
;*	       let_rtn is evaluated.
;*
;*COMMENT: %loc_flg set to true to enable semicolons to act as  
;*	   delimiters in a declaration sequence.
;*
;***************************************************************************

(de pre_let_rtn ()
    (let ((%constr %constr) (%inf %inf) (%loc_flg))		
	(let_rtn)
    );end let
);end pre_local_rtn

;***************************************************************************
;*	LET_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a let expression.
;*
;*RESULT: (mk-let DEC EXP) 
;*
;***************************************************************************

(de let_rtn ()
	(prog (res exp)
	   (gnt)
	   (setq res `(mk-let ,(loc_off (dec_rtn (loc_on)))));parse dec.
	   (ifn (eq token '|in|)
		(parse_failed '|let expression: missing "in" |))
	   (gnt)
	   (dec_test1 '|let expression: |)
	   (setq exp (parse 35));parse exp.
		  
	   (if (eq token scolon_sym);exp sequence!
		(setq exp (expseq_rtn))
	   );end if
	   (newr res exp);
	   (ifn (eq token 'end)
	      (parse_failed '|let expression: missing "end" |))
	   (gnt)
	   (return res)
	);end prog
);end let_rtn


;***************************************************************************
;*	FN_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a fn expression.
;*
;*RESULT: (mk-fn pat1.EXP1 .. patn.EXPn)
;*
;***************************************************************************

(de fn_rtn (lev)
	(prog (pat exp match) 
loop
	   (setq pat (parse 55));parse pattern
	   (ifn (eq token match_sym)
		(parse_failed '|match: missing "=>" |))
	   (gnt)
	   (setq exp (parse lev)); parse expression
	   (newr match (cons pat exp))
	   (cond
		((eq token singlebar_sym); new match ?
		   (gnt) (go loop))
		(t (return `(mk-fn . ,match)))
	   );end cond
	);end prog
);end fn_rtn

;***************************************************************************
;*	HANDLE_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Parse a handle expression. Returns :
;*		exn with match -> (mk-handle exp (mk-withhand exn . MATCH))
;*		exn => exp     -> (mk-handle exp (mk-wildhand exn EXP))
;*		?   => exp     -> (mk-handle exp (mk-univhand exp))
;*
;*CALLING: fn_rtn.
;*
;*LOCAL VARIABLES: exp : expression
;*   		   res : result of handle.
;*		   mres : contains the matches that are picked out from match.
;*		   tl : rhs of a hrule.
;*		   exn : exception name
;*
;*COMMENT:  fn_rtn is called to parse a match.
;*
;***************************************************************************
(de handle_rtn ()
   (prog (exp res exn tl match)
	(setq res (cons par_res res));expression
loop
	(setq exn token )
	(if (is_type_var exn)
	   (parse_failed (concat '|handle expression: | exn
	   '| is not a valid exception name|))
	);end if
	(setq tl
	   (cond
		((eq (gnt) 'with)
		   (gnt)
		   (cons 'mk-withhand (cons exn (cdr (fn_rtn 270)))))
		((eq token match_sym)
		   (gnt)
		    (if (eq exn trap_sym)
			`(mk-univhand ,(parse 270))
   		        `(mk-wildhand ,exn ,(parse 270))
		    ));end ifn
		(t (parse_failed
			(concat '|handle expression: |
			 token '| in the wrong place |)))
	   );end cond
	);end setq
	(newr res tl)
	(cond
	   ((eq token handle_sym)
		(gnt ) (go loop))
	   (t (return (cons 'mk-handle res)))
	);end cond
   );end prog
);end handle_rtn

;***************************************************************************
;*	CASE_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Parse a case expression. Returns:
;*		(mk-case EXP . MATCH)
;*
;*COMMENT: fn_rtn is called to parse a match.
;*
;***************************************************************************
(de case_rtn ()
	(prog (exp match res)
	   (setq exp (parse 50)); parse expression
	   (ifn (eq token 'of)
		(parse_failed '|case expression: missing "of" |))
	   (gnt)
	   (setq match (cdr (fn_rtn 330))); parse a match

	   (return `(mk-case ,exp . ,match))
	);end prog
);end case_rtn



;***************************************************************************
;*	TYPE_EXP_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a type expression, returns the following:
;*
;*		tyvar ->  (mk-vartyp id).
;*		(ty1, .. ,tyn) con -> (mk-consttyp tycon . (TY1 .. TYn))
;*		ty1->ty2 -> (mk-funtyp TY1 TY2)
;*		ty1*ty2 -> (mk-tupletyp TY1 TY2)
;*		ty=int,string,bool -> (mk-consttyp ty)
;*
;***************************************************************************
(de type_exp_rtn ()
	(funtyp_rtn (tupletyp_rtn (type_ex1)))
);end type_exp_rtn

;***************************************************************************
;*	FUNTYP_RTN
;***************************************************************************
;*
;*DESCRIPTION: Returns the following if the type expression
;*	       is of fun type:
;*		   ty1 -> ty2 : (mk-funtyp ty1 ty2)
;*
;***************************************************************************

(de funtyp_rtn (typ)
	(cond
	   ((eq token arrow_sym)
		(gnt)
		(list 'mk-funtyp typ (type_exp_rtn)))
	   (t typ)
	);end cond
);end funtyp_rtn

;***************************************************************************
;*	TUPLETYP_RTN
;***************************************************************************
;*
;*DESCRIPTION: Returns the following if the type expression
;*	       is of tuple type:
;*		   ty1 * ty2 -> (mk-tupletyp TY1 TY2)
;*
;*CALLING: type_exp_rtn
;*
;*CALLED BY: type_exp_rtn
;*
;***************************************************************************
(de tupletyp_rtn (typ)
   (prog (res)
	(cond
	   ((eq token mul_sym)
		(setq res `(,typ))
		(while (eq token mul_sym)
		   (gnt)
		   (newl res (type_ex1))
		);end while
		(return (cons 'mk-tupletyp (reverse res))))
	   (t (return typ))
	);end cond
   );end prog
);end tupletyp_rtn

;***************************************************************************
;*	TYPE_EX1
;***************************************************************************
;*
;*DESCRIPTION: Parse a type expression which is either:
;*		tyvar -> (mk-vartyp tyvar)           or:
;*		(ty1, .. ,tyn) tycon -> (mk-consttyp tycon (TY1 .. TYn)).
;*
;*LOCAL VARIABLES: seq : tyvar sequence.
;*	           res : result of type_ex1.
;*
;***************************************************************************

(de type_ex1 ()
	(prog (res x)
	   (setq res
		(cond
		   ((eq token lparen_sym); sequence of type expr.
			(type_seq_rtn))
		   ((eq token lrecord_sym);record type !
			(gnt)
			(recordtyp_rtn))
		   (t
			(type_ex2))
		);end cond
	     );end setq
	     (gnt)
loop
		(cond
		   ((or (memq token res_words) 
			(memq token 
		           (list comma_sym scolon_sym singlebar_sym
				 rparen_sym arrow_sym mul_sym
				 eq_sym match_sym rrecord_sym)))
			   (return res));token is not a tycon
		   (t                   ;token is a tycon. 
			  (gnt)
			  (if (is_type_var token)
			    (parse_failed
			       (concat '|type expression: | token 
			      '| is not a type constructor|))
			  );end if
			  (setq res
	                        `(mk-consttyp
				   ,ptoken . ,(if (or
						(not (> (length res) 1))
				(memq (car res) 
				  '(mk-vartyp mk-consttyp mk-tupletyp
				    mk-recordtyp mk-funtyp)))
					 `(,res) res)) 
			   );end setq
			;**   (setq seq nil)
		           (go loop))
		);end cond
	);end prog
);end type_ex1

;***************************************************************************
;*	TYPE_EX2
;***************************************************************************
;*
;*DESCRIPTION: type_ex2 gives the following results:
;*
;*		tyvar -> (mk-vartyp tyvar)
;:		tycon -> (mk-consttyp tycon)
;*
;*CALLING: is_type_var.
;*
;*CALLED BY: type_ex1.
;*
;***************************************************************************
(de type_ex2 ()
	(cond
	   ((is_type_var token)
		(if tyvar_ch ;tyvar check set to t in type_bind_rtn1
			(ifn (memq token %tyvar)
			   (parse_failed (concat '|type expression: | token
				'| is not listed on the left hand side|))
			);end ifn
		);end if
		(list 'mk-vartyp token));	type variable
	   (t
	      (cond
		 ((eq token 'unit) '(mk-recordtyp))
		 (t (list 'mk-consttyp token)); type constructor
	      ));end cond
	); end cond
);end type_ex2

;***************************************************************************
;*	TYPE_SEQ_RTN
;***************************************************************************
;*
;*DESCRIPTION: type_seq_rtn parses a ty-exp sequence and gives the
;*	       following result: seq -> (TY1 .. TYn)
;*			         (ty) -> TY
;*
;*CALLING: type_exp_rtn.
;*
;*CALLED BY: type_ex1.
;*
;*LOCAL VARIABLES: res : result of type_seq_rtn.
;*
;***************************************************************************
(de type_seq_rtn ()
	(prog (res) 
	   (gnt)
	   (newr res (type_exp_rtn))
	   (if (eq token rparen_sym);paranth. type exp!
		(return (car res)) 
	   );end if
	loop
	   (cond
		((eq token comma_sym)
		    (gnt)
	            (newr res (type_exp_rtn))
		    (go loop))
		((eq token rparen_sym)
		   (return res ))
		(t (parse_failed  (concat '|type expression: | token 
		'| found where comma or right paranthesis was expected|)))
	   );end cond
	);end prog
);end type_seq_rtn

;***************************************************************************
;*        RECORDTYP_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a record type. Returns:
;*		{lab1:ty, .. ,labn:tyn} -> (mk-recordtyp lab1.TY1 .. labn.TYn)
;*
;*CALLED BY: type_ex1
;*
;*LOCAL VARIABLES: num_flg : set to true if labels are numeric.
;*		   lab_l : list of used labels.
;*
;***************************************************************************
(de recordtyp_rtn ()
    (prog (res label num_flg lab_l)
	(cond
	   ((eq token rrecord_sym)
		(return '(mk-unit)))
	);end cond
	(if (is_numlabp token);numeric label ?
	   (setq num_flg t)
	);end ifn
loop
	(if (memq token lab_l)
	   (parse_failed
	      (concat 
		'|record type: multiple occurrence of label - |
		 token))
	);end if
	(setq lab_l (cons (setq label token) lab_l))
	(if num_flg;check for mixt. of numeric and alpha labels.
	   (if (not (is_numlabp label))
		(parse_failed 
		  (concat '|record type: | label
		   '| found where a numeric label was expected|))
		(setq label (concatl (cddr (explode label))));pick out number
	   );end if
	   (if (is_numlabp label)
		(parse_failed
		  (concat '|record type: | label
		   '| found where an alphabetic label was expected|))
	   );end if
    	);end if
	(gnt)
	(ifn (eq token colon_sym)
	   (parse_failed 
		(concat '|record type: | token
		  '| found where a colon was expected|
		);end concat
	   );end parse_failed
	);end ifn
	(gnt)
	(newr res (cons label (type_exp_rtn)))
	(cond
	   ((eq token comma_sym)
		(gnt)
	   	(go loop))
	   ((eq token rrecord_sym)
		(return (cons 'mk-recordtyp res)))
	   (t (parse_failed
		(concat '|record type: | token
		  '| found where a comma or curly bracket was expected|
		);end concat
	      ));end parse_failed
	);end cond
   );end prog
);end recordtyp_rtn

;***************************************************************************
;* 	TVR_SEQ_RTN       
;***************************************************************************
;*
;*DESCRIPTION: Parse a tyvar sequence. Returns:
;*		('a, .. ,'z) -> ('a .. 'z)
;*
;*CALLING: is_type_var.
;*
;*CALLED BY: type_exp_rtn.
;*
;*LOCAL VARIABLES: res : result of tvr_seq_rtn.
;*
;***************************************************************************
(de tvr_seq_rtn ()
	(prog (res) 
	    loop
	       (if (is_type_var token)
		  (newr res token)
		  (parse_failed (concat '|type variable sequence: | token
		    '| is not a type variable|))
	       );end if
	       (cond
	          ((eq (gnt) comma_sym) (gnt) (go loop))
	          ((eq token rparen_sym) (gnt) (return res))
		  (t (parse_failed  (concat '|type var sequence: | token 
'| found where comma or right paranthesis was expected|)
		   ))
	       );end cond
	);end prog
);end t vr_seq_rtn


;***************************************************************************
;*
;*	DECLARATIONS
;*
;
;***************************************************************************
;*	VAL vb
;***************************************************************************

;***************************************************************************
;* 	VAL_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Parse a value declaration. Returns:
;*		(mk-val VB)
;*
;***************************************************************************
(de val_rtn ()
	`(mk-val ,(val_bind_rtn))
);end val_rtn

;***************************************************************************
;*	VAL_BIND_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Parse a value binding. Returns:
;*		simple -> (mk-valbind PAT EXP)
;*		rec vb -> (mk-rec VB)
;*		vb and .. and vb -> (mk-and VB .. VB)
;*
;*LOCAL VARIABLES: 
;*		   pat : pattern
;*		   exp : expression
;*		   res : result of value binding
;*
;*	   Value bindings can only be paranth. in the rec case.  
;*         
;*COMMENTS: See fun_bind_rtn. (distinguishing between clausal fb and simple vb !)
;*
;***************************************************************************
(de val_bind_rtn ()
	(prog (pat exp res temp) 
loop
	   (cond
	  	((eq token 'rec); recursive val. binding
		   (gnt)
		   (setq temp (list 'mk-rec (val_bind_rtn)))
		   (go and))
		((eq token lparen_sym); paranth. val binding or tuple
		   (gnt)
		   (cond
			((eq token 'rec)
			    (gnt)
			    (setq temp `(mk-rec ,(val_bind_rtn)))
			    (go and))
			(t (setq pat (tuple_rtn)) (go ty))
		    ));end cond
	   );end cond

	   (def_prec eq_sym 30);change prec.lev. for eq_sym.
	   (def_prec colon_sym 30);we want to stop before a ty. constr.

	   (setq pat (parse 32)); parse pattern

	   (def_prec eq_sym inf_lev);old prec. lev. for eq_sym.
	   (def_prec colon_sym 530); - " - colon_sym.

	   (if (and
		(memq (car pat) '(mk-infappn mk-appn));applic. of var
		(memq (caadr pat) '(mk-var mk-opvar)))  ; -> func. bind.
		(parse_failed 
		   '|val declaration: wrong form of binding|
		);end parse_failed
	   );end if
ty
	   (cond 
	     ((eq token colon_sym);type constr!
		(gnt)
		(setq pat (type_constraint_rtn)))
	   );end cond
	   (check_eq_sym '|val declaration: missing "=" |); check for equal symbol
	   (dec_test1 '|val-binding : |);check that declaration does not follow!
	   (setq exp (parse 90)); parse expression
	   (setq temp
		   `(mk-valbind ,pat ,exp)
	   );end setq
and
	   (newl res temp)
	   (cond
		((eq token 'and); and 
		   (gnt)
		   (go loop)); parse next binding
	        ((> (length res) 1); and case
		   (return (cons `mk-and (reverse res))));
		((eq token rparen_sym)
		   (gnt)
		   (return (car res)))
		(t; 
		   (return (car res)))
	   );end cond
	);end prog
);end val_bind_rtn

;***************************************************************************
;*        FUN_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a fun declaration.
;*
;***************************************************************************
(de fun_rtn ()
   `(mk-fun ,(fun_bind_rtn))
);end fun_rtn

;***************************************************************************
;*        FUN_BIND_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a function binding.
;*	       Result:
;*		   clause1 | .. |clausen -> (mk-funbind CLAUSE1 .. CLAUSEn)
;*
;*		   fb1 and .. and fbn -> (mk-and FB1 .. FBn)
;*
;*COMMENT: To be able to diffirentiate between a simple vb and a clausal fb,
;*         we parse until we reach either a colon (type constr.) or the
;*	   equal sign (that is why we change the precedence levels for those 
;*	   two symbols). We then take advantage of the fact that, parsing
;*	   the lhs of a function binding returns: 
;*		(mk-appn ({mk-var/mk-opvar var) (mk-appn apat1 ( ... )))
;*	   We can therefore detect a function binding and pick out the
;*	   variable and the apat's. (This is done in clause_rtn).
;*         Note that a value binding never returns (mk-appn (mk-var ... )!
;*
;*
;***************************************************************************
(de fun_bind_rtn ()
   (prog (res fb)
loop
	(newr fb (clause_rtn))
	(cond
	   ((eq token singlebar_sym)
		(gnt)
	 	(go loop))
	   (t (newr res (cons 'mk-funbind fb)))
	);end cond
	(cond
	   ((eq token 'and)
		(gnt)
		(setq fb nil)
		(go loop))
	   (t
	 	(return
		   (if (> (length res) 1)
			(cons 'mk-and res)
			(car res)
		   );end if
		));end return
	);end cond
   );end prog
);end fun_bind_rtn

;***************************************************************************
;*	CLAUSAL_RTN        
;***************************************************************************
;*
;*DESCRIPTION: parse a clausal function binding. Returns:
;*	<op> var apat1 .. apatn <:ty>=exp -> 
;*	(mk-<op>clause var (APAT1 .. APATn) EXP <TY>)
;*
;*	(apat1a var apat1b) apat2 .. apatn <:ty> = exp ->
;:	(mk-infclause var (mk-tuple APAT1a APAT1b) APAT2 .. APATn) EXP <TY>)
;
;*	apat1 var apat2 <:ty>=exp -> CLAUSE1 where
;*		clause1= (apat1 var apat2) <:ty> =exp
;*
;*LOCAL VARIABLES:  pat : pattern
;*		    exp : expression
;*
;***************************************************************************
(de clause_rtn ()
   (prog (pat clause ty exp)
	(def_prec eq_sym 30);we want to stop at "=" 
	(def_prec colon_sym 30); or ":"(type constraint)
	(setq pat
	   (pat_check
		(parse 32)
	   );end patcheck
	);end setq
	(def_prec eq_sym inf_lev)
	(def_prec colon_sym 530)
	(setq clause
	  (cond
	      ((cdar pat)        ; tag=true ?  -fun (apat1 var apat2) ...= ..
		 `(mk-infclause ,(cadaar pat) ,(cdr pat)))
	      ((eq (caaar pat) 'mk-opvar)      ; -fun op var apat1 apat2 ..=..
		`(mk-opclause ,(cadaar pat) ,(cdr pat)))
	      (t				; -fun var apat1 apat2 ..   =..
		`(mk-clause ,(cadaar pat) ,(cdr pat)))
	   );end cond
	);end setq
	(cond ((eq token colon_sym); type constraint
	   (gnt)
	   (setq ty (type_exp_rtn)))
	);end cond
	(check_eq_sym '|fun declaration: missing "=" |)
	(dec_test1 '|fun-binding: |);check that declaration does not follow!
	(setq exp (parse 90))
	(newr clause exp)
	(return (if ty (newr clause ty) clause))
   );end prog
);end clause_rtn

;***************************************************************************
;:	PAT_CHECK
;***************************************************************************
;*
;*DESCRITION: Returns a list of apats but with the first element being a
;* pair of the function name and a tag which is true if the clause is of 
;* form (apat1 id apat1') apat2 .. , and false otherwise
;*
;***************************************************************************
(de pat_check (pat)
   (cond
	((eq (car pat) 'mk-infappn)
	   `((,(cadr pat) . t) (mk-tuple ,(caddr pat) ,(cadddr pat))))
	((eq (car pat) 'mk-appn)
	   (reverse (cons (caddr pat) (pat_check1 (cadr pat)))))
	(t (parse_failed '|fun declaration: wrong form of binding |))
  );end cond
);end pat_check

;*****************************************************************************
;*	PAT_CHECK1
;*****************************************************************************
(de pat_check1 (pat)
   (cond
	((null pat) 
	     (parse_failed '|fun declaration: wrong form of binding |))
	((memq (car pat) '(mk-con mk-const));constr. cannot be rebound as var
		(parse_failed (concat 
		 '|fun declaration: constructor | (cadr pat)
		 '| found where function name was expected|)))
	((memq (car pat) '(mk-var mk-opvar))
		`((,pat . nil)))
	((eq (car pat) 'mk-infappn)
	   `((mk-tuple ,(caddr pat) ,(cadddr pat)) (,(cadr pat) . t)))
	(t (cons (caddr pat) (pat_check1 (cadr pat))))
   );end cond
);end pat_check1

;***************************************************************************
;*	TYPE tb
;
;***************************************************************************
;*	TYPE_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Returns the result of parsing a type declaration. It is
;*	       evaluated when token is the reserved word 'type'. Returns:
;*		   (mk-type TB).
;*
;*CALLING: type_bind_rtn.
;*
;***************************************************************************

(de type_rtn ()
	(list 'mk-type (type_bind_rtn ))
);end type_rtn

;***************************************************************************
;*	TYPE_BIND_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Returns the result of parsing a type binding:
;*
;*
;*	{tyvar_seq} tycon = ty -> (mk-typebind (tyvar1 .. tyvarn) tycon TY)
;*
;*	tb1 and .. and tbn -> (mk-and TY1 .. TYn)
;*	
;*
;*LOCAL VARIABLES: lhs : left hand side of type binding.
;*		   res : result of type_bind_rtn.
;*	           temp : is used to build up the result.. it is
;*			   set to the result of parsing one binding. 
;*		   x : result of type_exp_rtn
;*		   
;*
;*COMMENTS: The right hand side is parsed by calling type_exp_rtn
;*	    (non-generative). 
;*	    Each new type constructor is added to the global list %conlay
;*	    and all previous constructors declared with tycon in a datatype
;*	    declaration, will be hidden.
;*	    
;*
;***************************************************************************
(de type_bind_rtn  ()
       (prog (tycon res temp x %conlay) 
loop
	   (cond 
	      ((eq token lparen_sym);sequence 
		(cond
		   ((is_type_var (gnt)); sequence
			(setq %tyvar (tvr_seq_rtn))
			(if (is_type_var token)
			   (parse_failed (concat '|type declaration: | token
			    '| cannot be a type constructor|))
			);end if
			(setq tycon token))
	      	   (t 
			(parse_failed
			   (concat '|type declaration: | token
			     '| is not a type variable|)
			));end parse_failed
	        ));end cond
	      ((is_type_var token); simple tyvar
		(setq %tyvar `(,token))
		(if (is_type_var (gnt))
		   (parse_failed (concat '|type declaration: | token
		    '| cannot be a type constructor|))
		);end if
		(setq tycon token))
	      (t (setq tycon token); type constructor only
		 (if (is_type_var token)
		   (parse_failed (concat '|type declaration: | token
		    '| cannot be a type constructor|))
		 );end if
	         (setq %tyvar '() ))
	   );end cond  	
	   (tycon_check tycon '|type declaration: |)
	   (gnt)
           (check_eq_sym '|type declaration: missing "=" |);
	   (setq tyvar_ch t); check in type_exp_rtn
	   (setq x (type_exp_rtn))	
	   (setq tyvar_ch nil)
	   (setq temp 
		 (list 'mk-typebind %tyvar tycon x)
	   );end setq
	 (newr %conlay `(,tycon))
	 (newl res temp)
	 (cond
	      ((eq token '|and|)
		   (gnt)
		   (go loop)); parse next type binding
	       ((> (length res) 1);and case
		   (add_conlay %conlay); add new layer to %conlay
		   (return (cons `mk-and (reverse res))))
	       (t 
		   (add_conlay %conlay); add new layer to %conlay
		   (return (car res)))
	  );end cond
	);end prog
);end type_bind_rtn

;***************************************************************************
;*        DATATYPE_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a datatype declaration. Returns (mk-datatype DB)
;*
;***************************************************************************
(de datatype_rtn ()
   `(mk-datatype ,(datatype_bind_rtn))
);end datatype_rtn

;***************************************************************************
;*        DATATYPE_BIND_RTN
;***************************************************************************
;*
;*DESCRIPTION: Parse a generative type binding (db). Returns the following
;*	       result:
;*		
;*		{tyvar_seq} tycon = con {of ty1} | .. | con of tyn ->
;*		(mk-datatypebind (tyvar1 .. tyvarn) tycon . ((con.TY1) .. (con.TYn)))
;*
;*		db and .. and db -> (mk-and DB .. DB)
;*
;*LOCAL VARIABLES: 
;*		   res : result of type_bind_rtn.
;*	           temp : is used to build up the result.. it is
;*			   set to the result of parsing one binding. 
;*		   x : result of type_exp_rtn
;*
;*COMMENTS: 
;*
;*	    Since constructors possess scope, a list %constr is used to
;*	    keep track of constructors declared on different levels.
;*	    It contains all declared constructors. However, if a new
;*	    constructor is declared on a lower level (ie not top level),
;*	    all previous occurrences of that constructor are hidden.
;*	    Format of %constr: ( .. (tycon list_of_new_constr list_of_old_constr) ..)
;*
;***************************************************************************
(de datatype_bind_rtn  ()
       (prog (tycon res temp x %conlay) 
loop
	   (cond 
	      ((eq token lparen_sym);sequence 
		(cond
		   ((is_type_var (gnt)); sequence
			(setq %tyvar (tvr_seq_rtn))
			(if (is_type_var token)
			   (parse_failed (concat '|datatype decalaration: | token
			    '| cannot be a type constructor|))
			);end if
			(setq tycon token))
	      	   (t 
			(parse_failed
			   (concat '|datatype declaration: | token
			     '| is not a type variable|)
			));end parse_failed
	        ));end cond
	      ((is_type_var token); simple tyvar
		(setq %tyvar `(,token))
		(if (is_type_var (gnt))
		   (parse_failed (concat '|datatype declaration: | token
		    '| cannot be a type constructor|))
		);end if
		(setq tycon token))
	      (t (setq tycon token); type constructor only
		 (if (is_type_var token)
		   (parse_failed (concat '|datatype declaration: | token
		    '| cannot be a type constructor|))
		 );end if
	         (setq %tyvar '()))
	   );end cond  	
	   (tycon_check tycon '|datatype declaration: |); test for predecl. type constr .
	   (gnt)
           (check_eq_sym '|datatype binding: missing "=" |);
	   (parse 565); parse a constructor (result in par_res)
	   (newl res
		`(mk-datatypebind ,%tyvar ,tycon . ,(data_rtn tycon))
	   );end newl
	   (cond
	      ((eq token '|and|)
		   (gnt)
		   (go loop)); parse next type binding
	       ((> (length res) 1);and case
   		   (add_conlay %conlay); add new layer to %conlay
		   (return (cons `mk-and (reverse res))))
	       (t 
		   (add_conlay %conlay); add new layer to %conlay
		   (return (car res)) )
	    );end cond
	);end prog
);end datatype_bind_rtn
	   

;**************************************************************************
;*	DATA_RTN        
;***************************************************************************
;*
;*DESCRIPTION: data_rtn parses the rhs of a datatype binding.
;*	       Returns: ((con1.TY1) .. (conn.TYn)) 
;*
;*LOCAL VARIABLES: res : result of data_rtn.
;*		   con_l : list of new constructors to be added to
;*		             format : ( .. (con.{0/1} .. )
;*	 	   %constr.
;*		   con : constructor
;*		   x : result of type_exp_rtn
;*
;***************************************************************************
(de data_rtn (tycon)
	(prog (res con_l con x) 
	   loop
	 	(if (is_type_var
		    (cadr (setq con par_res))); first constr.
		     (parse_failed (concat '|datatype declaration: | (cadr con)
			'| cannot be a constructor|))
		);end if
		(cond
		    ((eq token 'of) (gnt) 
				   (setq tyvar_ch t)
				   (setq x (type_exp_rtn))
				   (setq tyvar_ch nil)
				   (newr res 
				     (if (memq (car con) '(mk-opcon
						mk-opconst mk-opvar))
					`(mk-opconstr ,(cadr con) ,x)
					`(mk-constr ,(cadr con) ,x)
				      );end if
				   );end newr
			           (setq con_l
					(cons `(,(cadr con) . 1) con_l);non nullary
				   ));end setq
		    (t 
			(setq con_l
			   (cons `(,(cadr con) . 0) con_l);nullary
			);end setq
			(newr res
			  (if (memq (car con) '(mk-opvar mk-opcon mk-opconst))
			    `(mk-opconstr ,(cadr con))
			    `(mk-constr ,(cadr con))
			  );end if
			));end newr
		);end cond
		(cond
		     ((eq token singlebar_sym) 
			(gnt) 
			(parse 565);parse a constr.
			(go loop)); repeat
		     (t	
			(newr %conlay (cons tycon con_l))
			(return res))
		);end cond
	);end prog
);end data_rtn

;***************************************************************************
;*	PRE_ABSTYPE_RTN
;***************************************************************************
;*
;*DESCRIPTION: Saves the constructor list %constr and the infix list %inf.
;*
;*COMMENT: pre_abs_type_rtn is the code property of the reserved word abstype.
;*	   Since both constructors and infixes posses scope, %constr and 
;*	   %inf get back their old values after abstype_rtn is evaluated.
;*         %loc_flg set to true to enable semicolons to delimit decs
;*	   in dec sequences within abstype dec.
;*
;***************************************************************************
(de pre_abstype_rtn ()
    (let ((%constr %constr) (%inf %inf) (%loc_flg t))		
	(abstype_rtn)
    );end let
);end pre_abstype_rtn

;***************************************************************************
;*	ABSTYPE_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Parse an abstype declaration. Returns:
;*		(mk-abstype TB DEC)
;*
;*LOCAL VARIABLES: tb : type binding
;*		   dec : declaration
;*		   res : result of abstype_rtn.
;*
;***************************************************************************
(de abstype_rtn ()
	(prog (db dec res)
	   (setq db (datatype_bind_rtn))
	   (ifn (eq token 'with)
		(parse_failed '|abstype declaration: missing "with" |))
	   (gnt)
	   (setq dec
      	       (cond
		 ((eq token  'end)
		   '(mk-decseq)); empty sequence! 
		 (t 
	            (gnt);
	            (loc_off (dec_rtn (loc_on))))
		);end cond
	   );end setq
	   (ifn (eq token 'end)
	        (parse_failed '|abstype declaration: missing "end" |))
	   (gnt)
	   (return
		(list 'mk-abstype db dec))
	);end prog
);end abstype_rtn

;***************************************************************************
;*
;*	EXCEPTION eb;
;*
;***************************************************************************

;************************************************************
;*	EXCEPTION_RTN        
;************************************************************
;parse an exception declaration.

(de exception_rtn ()
	(list 'mk-exception (except_bind_rtn))
);end exception_rtn

;***************************************************************************
;*	EXCEPTION_BIND_RTN        
;***************************************************************************
;*
;*DESCRIPTION: returns:
;*		   exn {:ty} {=exn} -> (mk-exbind  (exn.TY) {exn}).
;*		   exn {= exn'} -> (mk-exbind exn {exn'})
;*		   eb1 and .. and ebn -> (mk-and EB1 .. EBn)
;*
;*LOCAL VARIABLES: res : result of except_bind_rtn.
;*
;************************************************************
(de except_bind_rtn ()
	(prog (res exn ex) 
and
	    (if (is_type_var token)	
	     (parse_failed (concat '|exception declaration: | token
		'| is not a valid exception name|))
	    );end if
	    (setq exn token)
	    (gnt)
	    (setq ex
		(cond
		   ((eq token colon_sym)
			(gnt)
			`(mk-exbind (,exn . ,(type_exp_rtn))))
		   (t `(mk-exbind (,exn . (mk-recordtyp))));unit by default
		);end cond
	    );end setq
	    (newl res
	       (cond
		((eq token eq_sym)
		   (gnt) (gnt)
		   (append ex `(,ptoken)))
	        (t ex)
	      );end cond
	    );end newl
	    (cond
		((eq token 'and)
		   (gnt)
		   (go and))
		((> (length res) 1);and case
		   (return (cons `mk-and (reverse res))))
		(t (return (car res))); remove mk-and!
	    );end cond
         );end prog
);end except_bind_rtn


;***************************************************************************
;*	PRE_LOCAL_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Saves the value of the constructor list %constr and the infix
;*	       list %inf
;*
;*CALLING: Let_rtn
;*
;*CALLED BY: Dec_rtn
;*
;*COMMENT: pre_local_rtn is the code property of the reserved word local.
;*	   Since both infixes and constructors posses scope, %constr and
;*	   %inf get back their old values after local_rtn is
;*	   evaluated.(+ additions in a local dec)
;*	   %loc_flg set to true to enable semicolons to act as delimiters
;*	   in a declaration sequence.
;*
;***************************************************************************
(de pre_local_rtn ()
    (let ((save_con0 %constr) (save_con1) (save_inf0 %inf)
			    (%loc_flg) (save_inf1))
	(local_rtn)
    );end let
);end pre_local_rtn

;***************************************************************************
;*	LOCAL_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Parse a local declaration. The following result is returned:
;*			(mk-local dec dec')
;*
;*
;*LOCAL VARIABLES: dec1 : first declaration.
;*		   dec2 : second declaration.
;*
;***************************************************************************
(de local_rtn ()
	(prog (dec1 dec2)
	    (setq dec1
      	       (cond
		 ((eq token  'in)
		   '(mk-decseq)); empty sequence! 
		 (t 
	            (gnt);
	            (loc_off (dec_rtn (loc_on))))
		);end cond
	    );end setq
	    (setq save_inf1 %inf);save pointer to %inf
	    (setq save_con1 %constr);save pointer to %constr
	    (ifn (eq token 'in)
	        (parse_failed '|local declaration: missing "in" |))
	    (gnt)
	    (setq dec2
      	       (cond
		 ((eq token  'end)
		   '(mk-decseq)); empty sequence! 
		 (t 
	            (gnt);
	            (loc_off (dec_rtn (loc_on))))
		);end cond
	    );end setq
	    (setq %constr (splice %constr save_con0 save_con1)); clean up %constr
	    (setq %inf (splice %inf save_inf0 save_inf1)); clean up %inf

	    (ifn (eq token '|end|)
	        (parse_failed '|local declaration: missing "end" |))
	    (gnt)
	    (return (list 'mk-local dec1 dec2))
	);end prog
);end local_rtn

;***************************************************************************
;*	INFIX_RTN        
;***************************************************************************
;*
;*DESCRIPTION: Gives a variable or a constructor infix status. 
;*	       This is done by adding a new infix layer to %inf 
;*	       every time infix or nonfix declaration is made.
;*	       Format of %inf:
;*	   (.. ((id1 .. idn) . ({nonfix/infix} . ({l/r} . prec_lev))) .. )
;*
;*LOCAL VARIABLES: prec : precedence level. 0 is default value.
;*		   inf : list of infixed variables.
;*
;*COMMENTS: Parameter x=l : left ass.  x=r : right ass.
;*	    infix identifiers are updated in update_inf.	
;*
;***************************************************************************
(de infix_rtn (x)
	(prog (prec inf)
	   (setq prec
		(cond
		   ((numbp token)
			(gnt)
			(if 
			  (or
			    (floatp ptoken);real number?
			    (< ptoken 0);less than zero?
			    (> ptoken 10);greater than 10?
			  );end or
			    (parse_failed 
				(concat
	'|infix: precedence must be an integer between 0 and 10 - |
			           ptoken))
			ptoken; ptoken>=0 !
			));end if
		   (t 0);default value
		);end cond
	   );end setq
	   (while (not (or (memq token `(,tml_sym in end))
			   (memq token dec_words)))
		    (if (is_type_var token)
			(parse_failed (concat '|infix: | token
			   '| cannot be be declared infixed|)
			);end parse_failed
		    );end if
		    (if (numbp token)
			(parse_failed (concat '|infix: | token
			  '| found where an identifier was expected|)
			);end parse_failed
		    );end if
		    (setq inf (cons token inf));add token to infix layer
		(gnt)
	   );end while
	   (ifn (null inf)
   	      (newl %inf `(,inf . (infix . (,x . ,prec))))
	   );end ifn
	   (return
		(if (eq x 'l)
		  `(mk-infix ,prec . ,inf)
		  `(mk-infixr ,prec . ,inf)
		);end if
	   );end return	
	);end prog
);end infix_rtn


;***************************************************************************
;*	NONFIX_RTN        
;***************************************************************************
;*DESCRIPTION: Gives id nonfix status by adding a new layer to %inf.
;*	       See infix_rtn.
;*
;*LOCAL VARIABLES: nonf : list of nonfixed id's
;*
;***************************************************************************
(de nonfix_rtn ()
	(prog (nonf)
	   (while (not (or (memq token `(,tml_sym in end))
			   (memq token dec_words)))
		    (if (is_type_var token)
			(parse_failed (concat '|nonfix: | token
			  '| cannot be nonfixed|))
		    );end if
		    (setq nonf (cons token nonf));
		(gnt)
	   );end while
	   (ifn (null nonf)
	      (newl %inf `(,nonf . (nonfix)))
	   );end ifn
	   (return `(mk-nonfix . ,nonf))
	);end prog
);end nonfix_rtn

;***************************************************************************
;*       DEC_RTN 
;***************************************************************************
;*
;*DESCRIPTION: Dec_rtn is evaluated if ptoken is a declaration word. It
;*	       selects the appropriate function to be evaluated and checks  
;*	       for a declaration sequence in which case it returns:
;*		(mk-decseq dec1 .. decn).
;*
;*LOCAL VARIABLES: dec : declaration.
;*
;*COMMENTS: In the case of a local and an abstype declaration, a pre-function 
;*	    is first evaluated to make a local constructor/infix  environment 
;*	    for that declaration.
;*	    %loc_flg is true when we are parsing a local declaration.
;*	    dummy exists to enable %loc_flg to be turned on (see local_rtn)
;*
;***************************************************************************
(de dec_rtn (dummy)
	(prog (dec )
	   (ifn (memq ptoken dec_words)
		(parse_failed (concat ptoken
		   '| found where a declaration was expected|))
	   );end ifn
	loop
	   (newr dec 
		(selectq ptoken 
		   (|val| (val_rtn))
		   (|fun| (fun_rtn))
		   (|datatype| (datatype_rtn))
		   (|type| (type_rtn))
		   (|abstype| (pre_abstype_rtn))
		   (|exception| (exception_rtn))
		   (|local| (pre_local_rtn))
		   (|infix| (infix_rtn 'l));left ass.
		   (|infixr| (infix_rtn 'r));right ass.
		   (|nonfix| (nonfix_rtn))
		);end selectq
	   );end newr
	   (cond
		((or (memq token dec_words); declaration sequence!
		     (if %loc_flg (eq token scolon_sym))); seq. in local.
		   (cond 
		     ((eq token scolon_sym);skip delimiter in local seq.
			(gnt)                 
			(if (memq token '(in end));have we reached 
			    		  	  ;end of local seq?
						  ;";" can term. loc. seq!
			   (return
				  (cons 'mk-decseq dec); 
			   );end return
			));end if		  
		   );end cond
	           (gnt)
		   (go loop))
	        ((or (eq token tml_sym);end of top level sequence.
		       (if %loc_flg (memq token '(in end))));end of seq.
							   ;in let/local
		   (return 
		      (if (> (length dec) 1)
			  (cons 'mk-decseq dec)
			  (car dec))
		      ));end ret
		(t (parse_failed (concat token
		   '| cannot delimit or terminate a declaration|)))
	   );end cond
	);end prog
);end dec_rtn

;***************************************************************************
;*	PARSEML
;***************************************************************************
(de parse_ml (pl)
   (def_prec tml_sym 35); ";" is dec delimiter in locals and lets
    (let ((lang1 'ml1)
	  (lang2 'ml2)
	  (prec_lev 'mllp)
	  (atom_rtn '(mlatomr))
	  (juxt_lev 580)
	  (juxt_rtn '(ml_juxt par_res))
	  (%loc_flg)
	  (parse_depth 0))
      (parse pl))
);end parseml

;***************************************************************************
;*	INFIX_RET        
;***************************************************************************
;*
;*DESCRIPTION: Checks infix precedence. If token is an infix id
;*             a check is made with the previous infixed id to see whether
;*	       we should continue parsing or returning.
;*	       If lev1=lev2 then we return if p_assoc=c_assoc=l (left) 
;*    	       or p_assoc<>c_assoc (different ass. but same prec.)
;*	       else we continue parsing.(p=previous, c=current)
;*
;*CALLED BY: parse
;*
;*LOCAL VARIABLES: p_inf : previous infixed id.
;*		   lev1 : infix prec. lev. for p_inf
;*		   lev2 : infix prec. lev. for token.
;*		   p_assoc : ass. value (l/r) for p_inf
;*		   c_assoc : ass. value for token. 
;*
;*COMMENT: Note that all infixed id's (including the predeclared) have the same
;*	   global precedence (the prec_lev prop.), but different infix
;*         precedence (the inf_prec prop of the id).
;*
;***************************************************************************
(de infix_ret ()
	(prog (p_inf lev1 lev2 p_assoc c_assoc)
	     (setq p_inf (top_inf))
	     (setq lev1 (get_infprec p_inf))
	     (setq lev2 (get_infprec token))
	     (setq p_assoc (get_infass p_inf))
	     (setq c_assoc (get_infass token))
	     (cond
		((eq lev1 lev2)
		   (cond
			((or
			   (and (eq p_assoc 'l);p_inf left assoc.?
				(eq c_assoc 'l));token left ass
			   (neq p_assoc c_assoc)
			 );end or
				(return t));finish parsing
	            ));end cond
		((> lev1 lev2)
		    (return  t));finish parsing
	      );end cond
	 );end prog
);end infix_ret


;***************************************************************************
;*	PARSEML
;***************************************************************************
;*
;*DESCRIPTION: This function parses the input until it reaches the parse
;*	       level 'end_lev' (ie end_lev <= cur_par_lev). The first
;*	       section takes action depending on what 'ptoken' (previous
;*	       token) is. If it is a reserved word, it evaluates the function
;*	       which is stored as the 'code' property of that word. The
;*	       result of the evaluation is stored in the variable 'par_res'.
;*	       Should ptoken be a number or an identifier then 'par_res' is
;*	       set to the result of evaluating the function 'atom_rtn'.
;*
;*	       The second section takes care of function applications (eg.
;*	       f x y;). In the same section a check is made for prefix
;*	       use of infix id's (no_op is set in op_rtn).
;*
;*	       In the third section we check whether we shall continue
;*	       parsing or returning. If token is an infix id, the rule is:
;*	       if cur_prec_lev=end_lev=user_lev then we have two consecutive
;*	       infixes and a comparison has to be made between the two id's
;*	       infix precedence levels (inf_prec). If lev1=lev2 then we
;*	       return if both are left associative or if they both have
;*	       different associatives. We also return if lev1>lev2. In
;*	       all other cases we continue parsing. 
;*	       To be able to match the check of infixes on the same parse
;*	       level, we push all infixes onto a stack. 
;*	       Eg. 1+2*3-4, when the result of parsing 2*3 is returned,
;*	       we want to compare -'s precedence level with +'s and not with
;*	       *'s.
;*
;*LOCAL VARIABLES: rtn : the code property of reserved word or special symbol.
;*	           cur_par_lev : current parse level.
;*
;***************************************************************************
(de parse (end_lev)
;sec1:
	(defconst prompt_char #/>); new prompt next new line!
	(prog (rtn cur_prec_lev)
	    (incr parse_depth)
	    (gnt)
	    (setq par_res 
		(if (and (symbolp ptoken)
			 (setq rtn (get ptoken lang1)))
			(eval rtn); evaluate appr. routine for token
			(eval atom_rtn)));token is a number or ident.
;sec2:
	loop 
	 (setq cur_prec_lev (if (symbolp token) (get_globprec token )))
	 (unless cur_prec_lev
		(when (lessp end_lev juxt_lev)
		   (setq par_res (eval juxt_rtn)) (go loop))
	        (decr parse_depth)
		(return par_res))

;sec3:
;return result if we have reached end level.
	(cond
	   ((and (eq cur_prec_lev end_lev) 
		 (eq cur_prec_lev inf_lev));two consec. infixes.
	      (cond ((infix_ret) ;check infix precedence.
			(pop_inf)	
	                (decr parse_depth)
			(return par_res))
	      ));end cond
           ((not (lessp end_lev cur_prec_lev))
	      (decr parse_depth)
	      (return par_res))
        );end cond	
;sec4:
;else continue parsing (rhs of binary operator)
	    (setq rtn (get_infcode token))
	    (if (is_infix token)
	       (push_inf token); push infix on stack
	    );end if
	    (if (null rtn)
		(parse_failed (concat '|syntax error: | token 
			      '| in the wrong place|))
	    );end if 
	    (gnt)
	    (setq par_res (eval rtn))
	    (go loop)
	);end prog
);end parse


;***************************************************************************
;initialize variables
(setq inf_stack nil)
(setq %constr nil)
(setq rem_inf_list nil)
(setq no_op t)  
(setq %conlay nil)
(setq %loc_flg nil)
(setq %real nil)
(setq tyvar_ch nil)
(setq atom_rtn '(mlatomr))
(setq parse_depth 0)
(setq inf_lev 550)
(setq %constr nil)
(setq rem_inf_list nil)
(setq no_op t)
(setq %inf_stack nil)
(setq piport nil)
(setq %inf nil);initially emtZ
