;****************************************************************************
;*
;*	S-site
;*
;****************************************************************************
; Site dependent information
; Origin: CAMBRIDGE LCF (Huet,Paulson,Cousineau...) 
; Mikael Hedlund, Rutherford Appleton Lab. (1986)

(eval-when (compile)
  (include llmac)
  (include S-constants))

; record when system was built
(defconst %cdate (date))


;***********************************************************************
;*	BANNER
;***********************************************************************
(defun banner ()
  (llterpri)
  (llprinc "# ")
  (llprinc %system-name) (llprinc %version)
  (llprinc " built on ") (llprinc %cdate)
  (llprinc " #")
  (llterpri) (llterpri)
  (llprinc '|For an introduction to the HELP system, type:    help"intro"; |)
  (llterpri))			; banner

; THIS VARIABLE SHOULD BE CHANGED BEFORE BUILDING SYSTEM:
(defconst %help-dir "/usr/lib/lcf/Help")
