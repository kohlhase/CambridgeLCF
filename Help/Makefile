#Makefile for the help system 
#sorts the unsorted kwick into lcf.kwic and creates subjects.hlp

all:   
	sort unsorted-lcf.kwic > lcf.kwic
	ls *.hlp | sed -e s/.hlp//g > subjects.hlp
