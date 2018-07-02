#******************************************************************************
#									      *
#	Makefile for Standard ML & LCF 					      *
#									      *
#******************************************************************************
#
# 	Remove all object files by typing:
# 
#                rm *.o
#
# 	 Change the value of the variable %help-dir to a new appropriate
#	 name. This variable point to the directory where the help information
#	 is stored (or will be stored):
#
#		/usr/fs1/pmh/LCF/Help  -> /usr/../mydir/Help
# 
#        Build LCF by typing:
# 
#                make lcfc
#
#        this will compile all lisp and SML files. The name of the binary image
#        is  "lcf".
#
#        Warning: All SML files (ie *.ml) must be compiled at the same time, so
#        do NOT compile and include an SML file in the system separatetly
#        once the system has been built. This will cause errors!!
#        (This does not apply to your own files, of course)
#
#        After an alteration of a lisp file, the system may be rebuilt by:
#
#                make lcf
#
#        this is much quicker since the SML files are not recompiled.
#
#
#        Standard ML may be built as a separate image. This is done by typing:
#                 
#                make smlc
#                 
#        The name of the image is "sml".
#                 
#        Building LCF or SML produces rather a lot of output, so it's a good
#        idea to redirect the output to a separate log file for later
#         investigation.
# 
#        Search for the key word "failed" for finding SML errors in the log
#        file, and "Error" for lisp errors in the same file.
#

ML_OBJ = sml

LCF_OBJ = lcf

LISP = lisp

LISPCOMP = liszt

MLOS =  llmac.o \
	S-constants.o \
	S-macro.o \
	S-site.o \
	S-franz.o \
	S-unix.o \
	S-dml.o \
	S-gp.o \
	S-help.o \
	S-parser.o \
	S-print.o \
	S-type.o \
	S-format.o \
	S-tran.o \
	S-iox-stand.o \
	S-list.o \
	S-obj.o \
	S-tml.o  

LCFOS =	L-dlcf.o \
	L-ol-syntax.o \
	L-ol-rec.o \
	L-typeol.o \
	L-parsol.o \
	L-writol.o \
    	L-subst.o \
	L-inst.o \
	L-thyfns.o \
	L-ol-net.o \
	L-simpl.o 

ML_LOADFILE = S-makeml.l

LCF_LOADFILE = L-makelcf.l

LOAD_ML =  (load "$(ML_LOADFILE)") \
	   (set-make) \
	   (tml) \
	   load("S-dml",true); load("S-curry",true); load("S-lis",true); load("S-gen",true); lisp"(setup-ml)"; save"$(ML_OBJ)"; quit() ;

LOAD_COMP_ML =  (load "$(ML_LOADFILE)") \
	   (set-make) \
	   (tml) \
	   compile("S-dml",true); compile("S-curry",true); compile("S-lis",true); compile("S-gen",true); lisp"(setup-ml)"; save"$(ML_OBJ)"; quit() ; 

LOAD_LCF = (load "$(LCF_LOADFILE)") \
           (set-make) \
           (tml) \
	   load("S-dml",true); load("S-curry",true); load("L-olcurry",true); load("S-lis",true); load("S-gen",true); load("L-ol-util",true); load("L-thyfns",true); load("L-pplamb",true); load("L-ppload",true); load("L-pcrule",true); load("L-rul",true); load("L-drul",true); load("L-pplemmas",true); load("L-ppsave",true); load("L-tacticals",true); load("L-tacont",true); load("L-tactics",true); load("L-conv",true); load("L-fconv",true); load("L-taut",true); load("L-resolve",true); load("L-ol-net",true); load("L-goals",true); load("L-stack",true); load("L-structac",true); load("L-structaxm",true); lisp"(setup)"; save"$(LCF_OBJ)"; quit(); 

LOAD_COMP_LCF = (load "$(LCF_LOADFILE)") \
           (set-make) \
           (tml) \
	   compile ("S-dml",true); compile("S-curry",true); compile("L-olcurry",true); compile("S-lis",true); compile("S-gen",true); compile("L-ol-util",true); compile("L-thyfns",true); compile("L-pplamb",true); compile("L-ppload",true); compile("L-pcrule",true); compile("L-rul",true); compile("L-drul",true); compile ("L-pplemmas",true); compile ("L-ppsave",true); compile("L-tacticals",true); compile ("L-tacont",true); compile ("L-tactics",true); compile("L-conv",true); compile("L-fconv",true); compile("L-taut",true); compile("L-resolve",true); compile("L-ol-net",true); compile("L-goals",true); compile("L-stack",true); compile("L-structac",true); compile("L-structaxm",true);   lisp "(setup)";   quit(); 


.l.o:
	echo "limit cpu 3m; $(LISPCOMP) $*.l" | csh


sml:    $(MLOS) $(ML_LOADFILE)
	echo '$(LOAD_ML)' | $(LISP) 

smlc: 	$(MLOS) $(ML_LOADFILE)
	echo '$(LOAD_COMP_ML)' | $(LISP); echo '$(LOAD_ML)' | $(LISP)

lcf:    $(MLOS) $(LCFOS) $(LCF_LOADFILE)
	echo '$(LOAD_LCF)' | $(LISP)

lcfc:    $(MLOS) $(LCFOS) $(LCF_LOADFILE)
	echo '$(LOAD_COMP_LCF)' | $(LISP); echo '$(LOAD_LCF)' | $(LISP)
