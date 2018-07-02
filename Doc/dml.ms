.NH
Defining SML primitives in Lisp
.LP
For the reason of speed and efficiency we want to be able to define
certain SML primitives directly in Lisp. There are several Lisp functions
for this purpose and they are described in this section.
.LP
.NH
Predefined Functions
.LP
A function written in lisp can be made available as an SML function using
\fIdml\fR which is a lisp function that takes information about the SML
primitive and extends the internal value and type environments:
.in +0.5i
.LP
(dml |div| 2 intdiv (mk-funtyp (mk-tupletyp (int) (int)) (int)))
.in -0.5i
.LP
The example shows how the SML function \fIdiv\fR has been defined in S-dml.l.
The first argument to \fIdml\fR is the name of the SML primitive that we are
defining (in this case \fIdiv\fR). The second argument is the number of
parameters that the defined function takes (div takes 2). 
The third argument is the
name of the lisp function that defines the SML function (in this case the lisp
function \fIintdiv\fR performs division on integers). The fourth and last
argument is the SML type of the defined function. The argument 
to \fIdml\fR should be 
the internal representation of that type
(see types.ms for information on internal representation of types)
.LP
The function \fIdiv\fR is an infixed function with precedence 7 in SML.
To give this information to the interpreter we call the function \fIdefinfprec\fR:
.in +0.5i
.LP
(definfprec '|div| 'l 7)
.in -0.5i
.LP
An infixed function can either be left or right associative. \fIdiv\fR is
left associative and hence the reason for the second argument 'l above.
.LP
