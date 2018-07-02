#sed script to help converting old ML to Standard ML
s/\*\*\*\*\*\*/'f/g
s/\*\*\*\*\*/'e/g
s/\*\*\*\*/'d/g
s/\*\*\*/'c/g
s/\*\*/'b/g
s/\*/'a/g
s/; *... *;/,...,/g
s/;;/;/g
s/let /val /g
s/letrec /fun /g
s/%\([^%]*\)%/(*\1*)/g
y/"`#/`"*/
