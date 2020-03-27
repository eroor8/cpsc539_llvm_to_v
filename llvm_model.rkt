#lang racket

(require
   racket/match
   redex/reduction-semantics)

(provide (all-defined-out))

(define-language MyLLVM
  [t ::= i32]                                    ; value types
  [a-or-r ::= a reg-i]
  [a ::= integer]
  [reg-i ::= variable-not-otherwise-mentioned]   ; reg index
  [lbl-i ::= variable-not-otherwise-mentioned]   ; reg index
  [line-i ::= variable-not-otherwise-mentioned]  ; reg index
  [R ::= empty                                   ; Register file
         (R reg-i a)]
  [l ::=                                         ; instructions   
     (br label lbl-i)                            ; branch to label e
     (reg-i = icmp slt t reg-i reg-i)            ; set reg value 1 if e1 < e2
     (br i1 reg-i label lbl-i label lbl-i)       ; branch to lbl_0 or lbl_1
     (reg-i = mul nsw t reg-i a)                 ; multiply 2 values
     (reg-i = add nsw t reg-i a)
     (reg-i = phi t [a-or-r lbl-i] [a-or-r lbl-i])
     (ret i32 reg-i)
     (l l)
     ]
  [c ::= lbl-i]
  [x ::= variable-not-otherwise-mentioned]
  [p ::= (label:lbl-i l p)]
)

(define-metafunction MyLLVM
  different : any any -> any
  [(different any_1 any_2) ,(not (equal? (term any_1) (term any_2)))])

(define-metafunction MyLLVM
  greater : any any -> any
  [(greater any_1 any_2) ,(> (term any_1) (term any_2))])

(define-metafunction MyLLVM
  multiply : any any -> any
  [(multiply any_1 any_2) , (* (term any_1) (term any_2))])

(define-metafunction MyLLVM
  add : any any -> any
  [(add any_1 any_2) , (+ (term any_1) (term any_2))])

(define-judgment-form MyLLVM
  #:contract (reg-lookup R reg-i a)
  #:mode (reg-lookup I I O)
  [-----
   (reg-lookup (R reg-i a) v a)]
  [(reg-lookup R reg-i_2 a_2)
   -----
   (reg-lookup (R reg-i_1 a_1) reg-i_2 a_2)])

(define-judgment-form  MyLLVM
  #:contract (reg-set R reg-i a R)
  #:mode (reg-set I I I O)
  [-----
   (reg-set (R reg-i a) reg-i a_2 (R reg-i a_2))]
  [-----
   (reg-set R reg-i a (R v ↦ a))])

(define-judgment-form  MyLLVM
  #:contract (label-lookup p lbl-i l)
  #:mode (label-lookup I I O)
  [-----
   (label-lookup (label: lbl-i l p) lbl-i l)]
  [(label-lookup p lbl-i_2 l_2)
   -----
   (label-lookup (lbl-i : l p) lbl-i_2 l_2)])

(define-judgment-form  MyLLVM
  #:contract (--> R p l c c R p l c c)
  [(reg-lookup R reg-i_2 a_2)
   (reg-set R reg-i (multiply a_2 a_1) R_2) 
   -----
   (--> R p ((reg-i = mul nsw t reg-i_2 a_1) l_2) c c_1 R_2 p l_2 c c_1)]
  [(reg-lookup R reg-i_2 a_2)
   (reg-set R reg-i (add a_2 a_1) R_2) 
   -----
   (--> R p ((reg-i = add nsw t reg-i_2 a_1) l_2) c c_1 R_2 p l_2 c c_1)]
  [(reg-lookup R reg-i_2 a_2)
   (reg-set R reg-i a_2 R_2)
   -----
   (--> R p ((reg-i = phi t [reg-i_2 lbl-i] [a-or-r lbl-i_2]) l_2) lbl-i c R_2 p l_2 lbl-i c)]
  [(reg-set R reg-i a_2 R_2)
   -----
   (--> R p ((reg-i = phi t [a_2 lbl-i] [a-or-r lbl-i_2]) l_2) lbl-i c R_2 p l_2 lbl-i c)]
  [(reg-lookup R reg-i_1 a_2)
   (reg-lookup R reg-i_2 a_3)
   (reg-set R reg-i a_2 R_2)
   -----
   (--> R p ((reg-i = icmp slt t reg-i_1 reg-i_2) l_2) c c_1 R_2 p l_2 c c_1)]
  [(reg-lookup R reg-i_1 a_2)
   (reg-lookup R reg-i_2 a_3)
   (reg-set R reg-i a_3 R_2)
   -----
   (--> R p ((reg-i = icmp slt t reg-i_1 reg-i_2) l_2) c c_1 R_2 p l_2 c c_1)]
  [(label-lookup p lbl-i l)
   -----
   (--> R p (br label lbl-i) c c_1 R_2 p l c_1 lbl-i)]
  [(label-lookup p lbl-i l)
   (reg-lookup R reg-i a_1)
   (where #f (different a_1 1))
   -----
   (--> R p (br i1 reg-i label lbl-i label lbl-i_2) c c_1 R_2 p l c_1 lbl-i)]
  [(label-lookup p lbl-i_2 l)
   (reg-lookup R reg-i a_1)
   (where #t (different a_1 1))
   -----
   (--> R p (br i1 reg-i label lbl-i label lbl-i_2) c c_1 R_2 p l c_1 lbl-i_2)])

; add evaluation condition
; model verilog
; model compilation
; show something!