;*****************************************************************************
;*
;*	S-constants
;*
;*****************************************************************************
;define global variables as lisp specials
; Mikael Hedlund, Rutherford Appleton Lab. (1986)
 
(special
 
;llmac

	   ~~l			;the gensymed name of selectq case

;lm,multics,franz,unix

	   %outport
	   poport		;output stream
	   piport		;input stream
	   outfiles		;set of output files
	   inputstack		;stack of input streams
	   %directory		;directory where input file found
	   %debug		;t iff compiler lisp sources files kept

;S-gp

	   prop			;holder of property for putpropl
	   initial%load		;t iff initial loading of the system
	   %symcount		;counter for internal gensym
	   %timestamp		;time stamp
	   word-sep		;for concatenation of the gensyms

;site

	   %help-dir		;path of help directory
	   %version		;current version 
	   %cdate		;date
	   %system-name		;LCF, ML, or what have you
	   experimental		;obsolete
 
;S-parser

	   prec_lev		;precedence  (mllp (sml) or ollp (ol))
	   %notcmnt		;flg to indicate when token is in comment
	   %conlay	  	; list of tycons and val cons

	   %real		;flag to indicate real number
	   %loc_flg		;flag to indicate parsing local 
						;dec. or let expression.
	   %no_op		;flg to indicate op before infix
	   id_syms		;identifier symbols
	   dec_words		;declaration key words
	   %inf_stack		;stack of infixed identifiers
	   %inf			;list of ids with infix status
	   tycons		;list of predeclared tycons
	   %constr		;list of ids with constructor status
	   inf_lev		;prec. level for infixed ids
	   par_res		;varible holding current parse tree
	   tyvar_ch
	   %tyvar		;list of type variables
	   %tyvar_ch		;flg for check of type variables
	   save_con0		;%constr before local parse
	   save_con1		;%constr after local parse
	   save_inf0		;%inf before local parse
	   save_inf1		;%inf after local parse
	   token		;current token
	   tokchs		;list of chars of next tokens
	   toktyp		;type of current token
	   char			;current char
	   pchar		;previous char
	   ptoken		;previous token
	   ptoktyp		;previous
	   parse_depth		;depth of parse recursion
	   lang1		;code of unary operator in current language
	   lang2		;code of binary operator in current language
	   langlp		;code of operator precedence in current language
	   atom_rtn		;lisp code of atom recognizer in current language
	   juxt_lev		;level of juxt nesting
	   juxt_rtn		;lisp code of juxt operator in current language
	   res_words		;reserved words
	   no_op		;flag 

;characters

	   space				;#\SPACE
	   cr					;#\CR
	   lf					;#\LF
	   tab					;#\TAB
	   lparen				;#\(
	   rparen				;#\)
	   period				;#\.
	   mulchr			        ;#\*
	   comma				;#\,
	   colon				;#\:
	   scolon				;#\;
	   lbrkt				;#\[
	   rbrkt				;#\]
	   multiply				;#\*
	   cmntchr				;#\%
	   tokqt				;#\`
	   escape				;#\\
           sharp_chr				;#\#
	   uparrow				;#\^ 
	   prime				;#\'
	

;*special symbols

	   tml_sym				;|;|
	   sharp_sym				;|#|
	   tokqt_sym				;|`|
	   arrow_sym				;|->|
	   cons_sym			    	;|::|
	   sum_sym				;|+|
	   prod_sym				;|#|
	   null_sym				;|unit|
	   neg_sym				;|not|
	   neq_sym				;|<>|
	   prime_sym
	   plus_sym				;|+|
	   mns_sym				;|-|
	   div_sym				;|/|
	   list_sym				;|list|
	   cnr_sym				;|"|
	   lt_sym				;|<|
	   gt_sym				;|>|
	   assign_sym				;|:=|
	   conc_sym				;|@|
	   wildcard_sym				;|_|
	   escape_sym				;|\|
	   mul_sym				;|*|
	   else_sym				;||||
	   eq_sym				;|=|
	   space_sym				;| |
	   cr_sym				;(ascii 13)
	   lf_sym				;(ascii 10)
	   tab_sym				;(ascii 9)
	   lparen_sym				;|)|
	   rparen_sym				;|(|
	   period_sym				;|.|
	   comma_sym				;|,|
	   colon_sym				;|:|
	   scolon_sym				;|;|
	   rrecord_sym				;|{|
	   lrecord_sym				;|}|
	   wildrecord_sym			;|...|
	   lbrkt_sym				;|[|
	   rbrkt_sym				;|]|
	   lcmnt_sym				;|(*|
	   rcmnt_sym				;|*)|
	   match_sym				;|=>|
	   singlebar_sym			;|||
	   trap_sym				;|?|
	   handle_sym				;||||
	   endcnr_sym	
	   eq_tok				;|=|
	   neq_tok				;|<<|
	   exists_tok				;|?|
	   conj_tok				;|/\|
	   disj_tok				;|\/|
	   imp_tok				;|==>|
	   iff_tok				;|<=>|
	   neg_tok				;|~|
	   arrow_tok				;|->|
 
	   %skiplimit		;number of strings to print when skipping
 
;S-type

	   %mlprindepth		;max depth of printing for ML
	   %mult_l		list of ids. multiple occurence
	   %vartypes		;list of vartypes
     	   %overload		;list of types
	   %eqtypes		;list of types
	   %generic
	   record		;%record
	   lay			;%lay
	   unittyp		;(mk-recordtyp)
	   realtyp		;(
	   %monotypes		;list of types
	   %mlprintdepth
	   exenv	        ;exception environment
	   env			;local environnement
	   tenv			;local type environnement
	   num_ops		;real,int
	   nums_ops		;real,int,string
	   asscheck		;check for assignment
	   structcheck		;check for structs
	   %l			;dummy for list
	   %env			;dummy for env
	   %exemt		;global exception environment
	   %thisexdec		;this exception declaratin
	   %id			;dummy for identifiers
	   %star		;number of stars in vartypes
	   %mono		;list of monotypes
	   nonloc		;t if not local
	   type%errors		;type errors
	   nulltyp		;null typep
	   booltyp		;booleen type
	   inttyp		;integer type
	   stringtyp		;string type
	   objty		;lisp object type
	   typety		;ol type type
	   termty		;ol term type
	   formty		;ol formula type
	   thmty		;ol theorem type
	   %thisdec		;t if ML declaration
	   %thistydec		;t if ML type declaration
	   %exemt		;global exception environment
	   %thisexdec		;this exception declaratin
	   %deftypes		;types defined in current exprs
	   %emt			;global environnement
	   %temt		;global type environnement
	   %sections		;stack of sections
	   lastvalname		;it

;S-mlprint

	   %print-depth		;depth of printing
	   %ex			;
 
;S-dml

	   %e			;run time environment
	   infixables				;
	   mlreserved
	   tracelist
	   initenv
	   tokempty				;|``|
 
;;;S-tran
	   val			;%val
	   exc			;%exc
	   msg1			;error message for multiple occs of vars in structs
	   msg2			;used instead of msg1 when mult occs allowed
	   %stringfns		;ass list of functions for makestring
	   %printfns		;A-list of print functions
	   %compfns		;fns to be declared before eval.
	   %p			;compile time environment
	   global%env		;global environment
	   new%%lb		;structure of ids in declaration
	   %ref			;flg to indicate refs
	   %loc_fundecs_flg	;flg to indicate local fun decs
	   fun%env		;list of unique syms repr. ML funs
	   ord			;%ord
	   rec			;%rec
	   dummy
	   %coneq_l		;list of type constructors
	   %eq_flg		;flag used for equlity test of tycons
	   %eq_flg1
	   %q-trans-args
	   %q-quote-arg
	   %timestamp
 
;S-format
	   %margin		;right margin
	   %infinity		;large value for default token size
	   %space		;space remaining on this line
	   %left-total		;total width of tokens already printed
	   %right-total		;total right of tokens ever put in queue
	   %pstack		;printing stack with indentation entries
	   %scan-stack		;
	   %qleft		;
	   %qright		;
	   %prettyon		;indicates if pretty-pretting is on
	   %curr-depth		;current depth of "begins"
	   %max-depth		;max depth of "begins" to print

;S-iox-stand

	   %%%fn
	   %%%args
	   fin-ligne
	   prompt_char
	   inputstack
	   prinlevel
	   prinlength
 
;S-tml
	   %f
	   %dev
	   %pt
	   %ty
	   %pr
	   %val
	   new%%lb
	   %compfns
	   global%env
	   %dump
	   %emt
	   %temt
	   %lb
	   %thisdec
	   %thistydec
	   tenv
	   %head
	   new%lb
	   %time
	   %timestamp
	   %symcount
	   %outport
	   prflag
	   ibase
	   base
	   *nopoint
	   prompt-char
	   instack
	   msgflag
	   initsection
	   initenv
	   nosecname
	   lastvalname
	   eof
	   nullty
 
;S-lis
	   %%F
 
	   %theorydata
	   %falsity				;ol-syntax
	   %vtyl				;ol-syntax
	   %thm-count				;ol-syntax
	   term-constrs				;parsol
	   cflag				;parsol
	   spec-toks				;parsol
	   anticnr-tok				;parsol
	   else-tok				;parsol
	   metaprec				;parsol
	   arrow-tok				;parsol
	   sum-tok				;parsol
	   prod-tok				;parsol
	   form-constrs				;
	   olinprec
	   %mk=antiquot
	   %empty				;f-typeol
	   %stickylist
	   %canonlist
	   %tyvars
	   %linkcount
	   %printtypes				;f-writol
	   %varpairs				;f-subst
	   %all
	   %vars
	   %newvars
	   %oldtys				;f-inst
	   %tyvl
	   %used-varnames
	   %changed-types
	   %renames
	   dash					;f-thyfns
	   legalconsts
	   %current
	   %ancestry
	   %kind
	   %loading-thy
	   olreserved
	   legalconst
	   %newconsts
	   %date
	   %theory-data
	   %theorems
	   %failtok
	   %newtypes
	   %current
	   %thy-cache
	   %new-ancestors
	   %sharetypes
	   %sharecount
	   %elem				;f-ol-net
	   %deferred
	   %substl				;f-simpl
	   %insttyl
	   %bv-pairs
	   %type-matches)

