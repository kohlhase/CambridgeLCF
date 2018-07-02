;****************************************************************************
;*
;*	S-help
;*
;****************************************************************************
; LCF help facility

(eval-when (compile)
     (include llmac)
     (include "S-macro")
     (genprefix help))

(dml |keyword| 1 ml-keyword (mk-funtyp (string) (mk-recordtyp)))
 
(defun ml-keyword (tok)
   (if (fileexists 'kwic "lcf") (keyword-search tok (fileof 'kwic "lcf"))
       (msg-failwith `|general|  "Help information is not available"))
); ml-keyword

(dml |help| 1 ml-help (mk-funtyp (string) (mk-recordtyp)))

; raises exception general if file is not found
(defun ml-help (tok)
   (if (fileexists 'help tok) (display-file (fileof 'help tok))
       (msg-failwith `|general|  (concat "No information available on " tok)))
); ml-help
