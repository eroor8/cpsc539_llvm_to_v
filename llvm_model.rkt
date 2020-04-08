#lang racket
(require
   racket/match
   redex/reduction-semantics)

(provide (all-defined-out))

(define-language MyLLVM
  ; Types: 32-bit ints are the only type supported
  [t ::= i32]
  ; Either a register index or a
  [a-or-r ::= a reg-i]
  ; Values: 32-bit ints are the only type supported
  [a ::= integer X]
  ; Indexes: mapping to register values, labels
  [reg-i ::= variable-not-otherwise-mentioned]   
  [lbl-i ::= variable-not-otherwise-mentioned integer X]
  ; Register file: maps register indexes to values
  [R ::= empty                                 
     (R reg-i a)]
  ; Instructions:
  [l-br ::=
     (br label lbl-i)                      ; branch to label 'lbl-i'
     (br i1 reg-i label lbl-i label lbl-i) ; if reg-i is 1, branch to lbl-i0 else lbl-i1
     (ret t reg-i)                       ; return reg-i
  ]  
  [l-notphi ::=
     l-br                                  ; all branching instructions
     (reg-i = icmp sle t reg-i reg-i)      ; set reg-i0 to 1 if reg-i1 < reg-i2
     (reg-i = mul nsw t reg-i a)           ; set reg-i to reg-i * a (of type t)
     (reg-i = add nsw t reg-i a)           ; set reg-i to reg-i + a (of type t)
     X
     ]  
  [l ::=
     l-br                                  ; all branching instructions
     l-notphi
     ; If the last label was lbl-i0, set reg-i to a-or-r0, else a-or-r1
     (reg-i = phi t [a-or-r lbl-i] [a-or-r lbl-i])
     (l l)                                 ; l is a sequence of instructions
     X
     ]  
  ; p is the program: a sequence of labels followed by sequences of instructions
  [p ::= empty (label lbl-i l p)]
  [c ::= lbl-i]
  [lbl-list ::= empty (lbl-list lbl-i lbl-i)]
)


; Define some metafunctions to be used during instruction step judgments
(define-metafunction MyLLVM    ; define less than
  lessereq : any any -> any
  [(lessereq any_1 any_2) ,(not (> (term any_1) (term any_2)))])
(define-metafunction MyLLVM    ; define multiplication
  multiplyl : any any -> any
  [(multiplyl any_1 any_2) , (* (term any_1) (term any_2))])
(define-metafunction MyLLVM    ; define addiltion
  addil : any any -> any
  [(addil any_1 any_2) , (+ (term any_1) (term any_2))])
(define-metafunction MyLLVM
  differentl : any any -> any
  [(differentl any_1 any_2) ,(not (equal? (term any_1) (term any_2)))])


; Lookup reg-i index to find corresponding value
(define-judgment-form MyLLVM
  #:contract (reg-lookup-l R reg-i a)
  #:mode (reg-lookup-l I I O)
  ; Matching key is last pair
  [----- "Lookup-Reg-Last"
   (reg-lookup-l (R reg-i a) reg-i a)]
  ; Matching key is not last pair
  [(reg-lookup-l R reg-i_2 a_2)
   (where #t (differentl a_2 X))
   ----- "Lookup-Reg-NotLast"
   (reg-lookup-l (R reg-i_1 a_1) reg-i_2 a_2)]
  ; Matching key is not in empty dict
  [
   ----- "Lookup-Reg-Empty"
   (reg-lookup-l empty reg-i X)]
  [(reg-lookup-l R reg-i X)
   (where #t (differentl reg-i reg-i_2))
   ----- "Lookup-Reg-Not-Found"
   (reg-lookup-l (R reg-i_2 a) reg-i X)]
   )

; Set register reg-i to value a in new register file
(define-judgment-form  MyLLVM
  #:contract (reg-set-l R reg-i a R)
  #:mode (reg-set-l I I I O)
  ; Replace existing key
  [
   ----- "Set-Reg-Existing"
   (reg-set-l (R reg-i a) reg-i a_2 (R reg-i a_2))]
  [(reg-lookup-l R reg-i_2 a_4)
   (where #t (differentl a_4 X))
   (where #t (differentl reg-i reg-i_2))
   (reg-set-l R reg-i_2 a_2 R_2)
   ----- "Set-Reg-Existing-Inner"
   (reg-set-l (R reg-i a) reg-i_2 a_2 (R_2 reg-i a))]
  ; Add new key
  [(reg-lookup-l R reg-i X)
   ----- "Set-Reg-New"
   (reg-set-l R reg-i a (R reg-i a))]
)
 
(define-judgment-form  MyLLVM
  #:contract (label-lookup p lbl-i l)
  #:mode (label-lookup I I O)
  ; Find section of program corresponding to lbl-i
  [----- "Lookup-Label-First"
   (label-lookup (label lbl-i l p) lbl-i l)]
  [(label-lookup p lbl-i_2 l_2)
   (where #t (differentl l_2 X))
   ----- "Lookup-Label-NotFirst"
   (label-lookup (label lbl-i l p) lbl-i_2 l_2)]
 ; Matching key is not in empty dict
  [
   ----- "Lookup-Label-Empty"
   (label-lookup empty lbl-i X)]
  [(label-lookup p lbl-i X)
   (where #t (differentl lbl-i lbl-i_2))
   ----- "Lookup-Label-Not-Found"
   (label-lookup (label lbl-i_2 l p) lbl-i X)]
  )


(define-judgment-form  MyLLVM
  #:contract (label-list-lookup lbl-list lbl-i lbl-i)
  #:mode (label-list-lookup     I        I     O)
  ; Find section of program corresponding to lbl-i
  [----- "Lookup-Label-First"
   (label-list-lookup (lbl-list lbl-i lbl-i_2) lbl-i lbl-i_2)]
  [(label-list-lookup lbl-list lbl-i_2 lbl-i_3)
   (where #t (differentl lbl-i_3 X))
   ----- "Lookup-Label-NotFirst"
   (label-list-lookup (lbl-list lbl-i lbl-i_4) lbl-i_2 lbl-i_3)]
 ; Matching key is not in empty dict
  [
   ----- "Lookup-Label-Empty"
   (label-list-lookup empty lbl-i X)]
  [(label-list-lookup lbl-list lbl-i X)
   (where #t (differentl lbl-i lbl-i_2))
   ----- "Lookup-Label-Not-Found"
   (label-list-lookup (lbl-list lbl-i_2 lbl-i_5) lbl-i X)]
  )

(define-judgment-form  MyLLVM
  ; Step one instruction
  ; p (R l c c) -> (R l c c)
  ; Where R is the register file, p is the program,
  ; l is the current instruction, first c is the previous label
  ; second c is the current label
  #:contract (-->l p R l c c R l c c)
  #:mode     (-->l I I I I I O O O O)
  ; Lookup input register in the register file, multiplyl by the value, set reg-i
  [(reg-lookup-l R reg-i_2 a_2)
   (reg-set-l R reg-i (multiplyl a_2 a_1) R_2) 
   ----- "Step-Mul"
   (-->l p R ((reg-i = mul nsw t reg-i_2 a_1) l_2) c c_1 R_2 l_2 c c_1)]
  ; Lookup input register in the register file, add to the value, set reg-i
  [(reg-lookup-l R reg-i_2 a_2)
   (reg-set-l R reg-i (addil a_2 a_1) R_2) 
   ----- "Step-Add"
   (-->l p R ((reg-i = add nsw t reg-i_2 a_1) l_2) c c_1 R_2 l_2 c c_1)]
  ; Lookup first input register in the register file, set reg-i if label matches
  [(reg-lookup-l R reg-i_2 a_2)
   (reg-set-l R reg-i a_2 R_2)
   ----- "Step-Phi-Reg-First"
   (-->l p R ((reg-i = phi t [reg-i_2 lbl-i] [a-or-r lbl-i_2]) l_2) lbl-i c R_2 l_2 lbl-i c)]
  ; Set reg-i to the first value if label matches
  [(reg-set-l R reg-i a_2 R_2)
   ----- "Step-Phi-Value-First"
   (-->l p R ((reg-i = phi t [a_2 lbl-i] [a-or-r lbl-i_2]) l_2) lbl-i c R_2 l_2 lbl-i c)]
  ; Lookup second input register in the register file, set reg-i if label matches
  [(reg-lookup-l R reg-i_2 a_2)
   (reg-set-l R reg-i a_2 R_2)
   ----- "Step-Phi-Reg-Second"
   (-->l p R ((reg-i = phi t [a-or-r lbl-i] [reg-i_2 lbl-i_2]) l_2) lbl-i_2 c R_2 l_2 lbl-i_2 c)]
  ; Set reg-i to the second value if label matches
  [(reg-set-l R reg-i a_2 R_2)
   ----- "Step-Phi-Value-Second"
   (-->l p R ((reg-i = phi t [a-or-r lbl-i] [a_2 lbl-i_2]) l_2) lbl-i_2 c R_2 l_2 lbl-i_2 c)]
  ; Set reg-i to 1 if reg-i_1 < reg-i_2
  [(reg-lookup-l R reg-i_1 a_2)
   (reg-lookup-l R reg-i_2 a_3)
   (reg-set-l R reg-i 1 R_2)
   (where #t (lessereq a_2 a_3))
   ----- "ICMP-Less"
   (-->l p R ((reg-i = icmp sle t reg-i_1 reg-i_2) l_2) c c_1 R_2 l_2 c c_1)]
  ; Set reg-i to 0 if reg-i_1 >= reg-i_2
  [(reg-lookup-l R reg-i_1 a_2)
   (reg-lookup-l R reg-i_2 a_3)
   (reg-set-l R reg-i 0 R_2)
   (where #f (lessereq a_2 a_3))
   ----- "ICMP-NotLess"
   (-->l p R ((reg-i = icmp sle t reg-i_1 reg-i_2) l_2) c c_1 R_2 l_2 c c_1)]
  ; Branch to lbl-i and update the previous label to the current one
  [(label-lookup p lbl-i l)
   ----- "Branch"
   (-->l p R (br label lbl-i) c c_1 R l c_1 lbl-i)]
  ; Branch if reg-i value is 1 to lbl-i
  [(label-lookup p lbl-i l)
   (reg-lookup-l R reg-i a_1)
   (where #f (differentl a_1 1))
   ----- "Branch-i1"
   (-->l p R (br i1 reg-i label lbl-i label lbl-i_2) c c_1 R l c_1 lbl-i)]
  ; Branch if reg-i value is not 1 to lbl-i_2
  [(label-lookup p lbl-i_2 l)
   (reg-lookup-l R reg-i a_1)
   (where #t (differentl a_1 1))
   ----- "Branch-i0"
   (-->l p R (br i1 reg-i label lbl-i label lbl-i_2) c c_1 R l c_1 lbl-i_2)]
)

(define-judgment-form  MyLLVM
  ; Step many times
  ; p c R -> a
  ; Where p is the program, c is the starting label and
  ; R are the input registers
  #:contract (-->l+ p R l c c R l c c)
  #:mode     (-->l+ I I I I I O O O O)
  [(-->l p R l c_0 c_1 R_10 l_10 c_10 c_11)
   (-->l+ p R_10 l_10 c_10 c_11 R_2 l_2 c_2 c_3)
   ----- "Run"
   (-->l+ p R l c_0 c_1 R_2 l_2 c_2 c_3)]
  [(-->l p R l c_0 c_1 R_2 l_2 c_2 c_3)
   ----- "Run-Single"
   (-->l+ p R l c_0 c_1 R_2 l_2 c_2 c_3)]
  )

(define-judgment-form  MyLLVM
  ; Step until we reach return
  ; p c R -> a
  ; Where p is the program, c is the starting label and
  ; R are the input registers
  #:contract (eval p R a)
  #:mode     (eval I I O)
  ; (ret t reg-i)
  [(label-lookup p entry l)
   (-->l+ p R l entry entry R_2 (ret i32 reg-i) c_0 c_1)
   (reg-lookup-l R_2 reg-i a)
   ----- "Step-Mul"
   (eval p R a)]
)




;(test-judgment-holds same-results
;  (derivation `(same-results 9 empty empty (ret t reg-i) 0 0 ) "Same"
;              (list
;               
 ;              )))
  
;(test-judgment-holds same-results
;  (derivation `(same-results 9 empty empty (ret t reg-i) 0 0 ) "Same"
;              (list
;               
;               )))


