;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

;; see https://www.compart.com/en/unicode/U+xxxx

((coq-mode . 
  ((company-coq-dir-local-symbols .
    ((":=" . ?≜) ("Proof." . ?∵) ("Qed." . ?■)
     ("!=" . ?≠) ("*" . ?×) ("\\sum_" . ?∑) ("\\in" . ?∊) ("\\subset" . ?⊂)
     ("`\\/" . ?∨) ("`/\\" . ?∧)
     ("`||" . ?‖)
     ("-[[" . ?⟦) ("[[" . ?⟦) ("]]" . ?⟧) ("{[" . ?⦃) ("]}" . ?⦄)
     ("Defined." . ?□) ("Time" . ?⏱) ("Admitted." . ?😱)))
   (prettify-symbols-mode . t)
)))

