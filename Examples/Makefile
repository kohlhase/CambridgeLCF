#******************************************************************************
#									      *
#	Makefile for LCF Theories					      *
#									      *
#******************************************************************************
#
#	To test a new LCF system, type "make test"
#
# 	To remove all theory files, type "make clean"
#
# 	To make all theory files, type "make all"
#

LCF = lcf		#could be redirected to ../Franz/lcf

THEORIES = 	fixedpoint.th \
		tr.th \
		eq.th \
		nat.th \
		LT.th \
		list.th \
		llist.th \
		seq.th  


test:    clean  all

clean:
	-rm *.th

all:    $(LCF) $(THEORIES)

.ml.th:
	$(LCF) < $*.ml 


.SUFFIXES:	.th .ml
