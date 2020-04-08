#lang racket
(require
   "llvm_model.rkt"
   racket/match
   redex/reduction-semantics)
(provide (all-defined-out))

(define-judgment-form MyLLVM
  #:contract (replace-phis l lbl-list l)
  #:mode     (replace-phis I I        O)
  ; Update labels.
  ; Assume no collisions here...
  [(label-list-lookup lbl-list lbl-i lbl-i_2)
   (where #t (different lbl-i_2 X))
   (replace-phis l lbl-list l_2)
   (label-list-lookup lbl-list lbl-i_1 X)
   -----
   (replace-phis
      ((reg-i = phi t [a-or-r lbl-i] [a-or-r_1 lbl-i_1]) l)
      lbl-list
      ((reg-i = phi t [a-or-r lbl-i_2] [a-or-r_1 lbl-i_1]) l_2)
   )
   ]
  [(replace-phis l lbl-list l_2)
   (label-list-lookup lbl-list lbl-i_1 lbl-i_2)
   (label-list-lookup lbl-list lbl-i lbl-i_3)
   (where #t (different lbl-i_2 X))
   (where #t (different lbl-i_3 X))
   -----
   (replace-phis
      ((reg-i = phi t [a-or-r lbl-i] [a-or-r_1 lbl-i_1]) l)
      lbl-list
      ((reg-i = phi t [a-or-r lbl-i_3] [a-or-r_1 lbl-i_2]) l_2)
   )
   ]
  [(replace-phis l lbl-list l_2)
   (label-list-lookup lbl-list lbl-i_1 lbl-i_2)
   (label-list-lookup lbl-list lbl-i X)
   (where #t (different lbl-i_2 X))
   -----
   (replace-phis
      ((reg-i = phi t [a-or-r lbl-i] [a-or-r_1 lbl-i_1]) l)
      lbl-list
      ((reg-i = phi t [a-or-r lbl-i] [a-or-r_1 lbl-i_2]) l_2)
   )
   ]
  [(label-list-lookup lbl-list lbl-i X)
   (label-list-lookup lbl-list lbl-i_1 X)
   (replace-phis l lbl-list l_2)
   -----
   (replace-phis
      ((reg-i = phi t [a-or-r lbl-i] [a-or-r_1 lbl-i_1]) l)
      lbl-list
      ((reg-i = phi t [a-or-r lbl-i] [a-or-r_1 lbl-i_1]) l_2)
   )
   ]
  [(replace-phis l lbl-list l_2)
   -----
   (replace-phis (l-notphi l)
      lbl-list
      (l-notphi l_2)
   )
   ]
  [-----
   (replace-phis l-notphi
      lbl-list
      l-notphi
   )
   ]
  )

(define-judgment-form MyLLVM
  #:contract (replace-all-phis p lbl-list p)
  #:mode     (replace-all-phis I I        O)
  [-----
   (replace-all-phis empty
      lbl-list
      empty
   )
  ]
  [(replace-all-phis p lbl-list p_2)
   (replace-phis l lbl-list l_2)
   -----
   (replace-all-phis
      (label lbl-i_3 l p)
      lbl-list
      (label lbl-i_3 l_2 p_2)
   )
   ]
)


; Lookup reg-i index to find corresponding value
(define-judgment-form MyLLVM
  #:contract (-->pass1a integer p p lbl-list)
  #:mode (-->pass1a     I       I O O)
  ; Update labels.
  ; Assume no collisions here...
  [-----
   (-->pass1a integer_0 empty empty empty)
   ]
  [(-->pass1a (addil integer_0 1) p p_2 lbl-list)
   -----
   (-->pass1a integer_0 (label lbl-i l-br p)
              (label lbl-i l-br p_2)
              lbl-list
   )
   ]
  [(-->pass1a (addil integer_0 1) (label integer_0 l_2 p_1) p_2 lbl-list)
   (label-list-lookup lbl-list integer_0 X)
   -----
   (-->pass1a integer_0 (label lbl-i (l l_2) p_1)
              (label lbl-i (l (br label integer_0)) p_2)
              (lbl-list lbl-i integer_0)
   )
   ]
  [(-->pass1a (addil integer_0 1) (label integer_0 l_2 p_1) p_2 lbl-list)
   (label-list-lookup lbl-list integer_0 integer_1)
   -----
   (-->pass1a integer_0 (label lbl-i (l l_2) p_1)
              (label lbl-i (l (br label integer_0)) p_2)
              (lbl-list lbl-i integer_1)
   )
  ]
  )


; Lookup reg-i index to find corresponding value
(define-judgment-form MyLLVM
  #:contract (-->pass1 p p)
  #:mode (-->pass1     I O)
  ; Update labels.
  ; Assume no collisions here...
  [(-->pass1a 0 p p_2 lbl-list)
   (replace-all-phis p_2 lbl-list p_3)
   -----
   (-->pass1 p p_3)
   ]
  )

