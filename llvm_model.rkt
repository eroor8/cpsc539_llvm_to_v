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
  [a ::= integer]
  ; Indexes: mapping to register values, labels
  [reg-i ::= variable-not-otherwise-mentioned]   
  [lbl-i ::= variable-not-otherwise-mentioned]
  ; Register file: maps register indexes to values
  [R ::= empty                                 
     (R reg-i a)]
  ; Instructions:
  [l ::=
     (br label lbl-i)                      ; branch to label 'lbl-i'
     (reg-i = icmp slt a reg-i reg-i)      ; set reg-i0 to 1 if reg-i1 < reg-i2
     (br i1 reg-i label lbl-i label lbl-i) ; if reg-i is 1, branch to lbl-i0 else lbl-i1
     (reg-i = mul nsw t reg-i a)           ; set reg-i to reg-i * a (of type t)
     (reg-i = add nsw t reg-i a)           ; set reg-i to reg-i + a (of type t)
     ; If the last label was lbl-i0, set reg-i to a-or-r0, else a-or-r1
     (reg-i = phi t [a-or-r lbl-i] [a-or-r lbl-i])
     (ret i32 reg-i)                       ; return reg-i
     (l l)                                 ; l is a sequence of instructions
     ]  
  ; p is the program: a sequence of labels followed by sequences of instructions
  [p ::= (label: lbl-i l p)]
  [c ::= lbl-i]
)

; Define some metafunctions to be used during instruction step judgments
(define-metafunction MyLLVM    ; define not equal
  different : any any -> any
  [(different any_1 any_2) ,(not (equal? (term any_1) (term any_2)))])
(define-metafunction MyLLVM    ; define less than
  lesser : any any -> any
  [(lesser any_1 any_2) ,(< (term any_1) (term any_2))])
(define-metafunction MyLLVM    ; define greater than
  greater : any any -> any
  [(greater any_1 any_2) ,(> (term any_1) (term any_2))])
(define-metafunction MyLLVM    ; define multiplication
  multiply : any any -> any
  [(multiply any_1 any_2) , (* (term any_1) (term any_2))])
(define-metafunction MyLLVM    ; define addition
  add : any any -> any
  [(add any_1 any_2) , (+ (term any_1) (term any_2))])

; Lookup reg-i index to find corresponding value
(define-judgment-form MyLLVM
  #:contract (reg-lookup R reg-i a)
  #:mode (reg-lookup I I O)
  ; Matching key is last pair
  [----- "Lookup-Reg-Last"
   (reg-lookup (R reg-i a) reg-i a)]
  ; Matching key is not last pair
  [(reg-lookup R reg-i_2 a_2)
   ----- "Lookup-Reg-NotLast"
   (reg-lookup (R reg-i_1 a_1) reg-i_2 a_2)])

; Set register reg-i to value a in new register file
(define-judgment-form  MyLLVM
  #:contract (reg-set R reg-i a R)
  #:mode (reg-set I I I O)
  ; Replace existing key
  [----- "Set-Reg-Existing"
   (reg-set (R reg-i a) reg-i a_2 (R reg-i a_2))]
  ; Add new key
  [----- "Set-Reg-New"
   (reg-set R reg-i a (R reg-i a))])

; Lookup lbl-i index to find corresponding set of instructions in the program
(define-judgment-form  MyLLVM
  #:contract (label-lookup p lbl-i l)
  #:mode (label-lookup I I O)
  ; Find section of program corresponding to lbl-i
  [----- "Lookup-Label-First"
   (label-lookup (label: lbl-i l p) lbl-i l)]
  [(label-lookup p lbl-i_2 l_2)
   ----- "Lookup-Label-NotFirst"
   (label-lookup (label: lbl-i l p) lbl-i_2 l_2)])

(define-judgment-form  MyLLVM
  ; Step one instruction
  ; p (R l c c) -> (R l c c)
  ; Where R is the register file, p is the program,
  ; l is the current instruction, first c is the previous label
  ; second c is the current label
  #:contract (--> p R l c c R l c c)
  ; Lookup input register in the register file, multiply by the value, set reg-i
  [(reg-lookup R reg-i_2 a_2)
   (reg-set R reg-i (multiply a_2 a_1) R_2) 
   ----- "Step-Mul"
   (--> p R ((reg-i = mul nsw t reg-i_2 a_1) l_2) c c_1 R_2 l_2 c c_1)]
  ; Lookup input register in the register file, add to the value, set reg-i
  [(reg-lookup R reg-i_2 a_2)
   (reg-set R reg-i (add a_2 a_1) R_2) 
   ----- "Step-Add"
   (--> p R ((reg-i = add nsw t reg-i_2 a_1) l_2) c c_1 R_2 l_2 c c_1)]
  ; Lookup first input register in the register file, set reg-i if label matches
  [(reg-lookup R reg-i_2 a_2)
   (reg-set R reg-i a_2 R_2)
   ----- "Step-Phi-Reg-First"
   (--> p R ((reg-i = phi t [reg-i_2 lbl-i] [a-or-r lbl-i_2]) l_2) lbl-i c R_2 l_2 lbl-i c)]
  ; Set reg-i to the first value if label matches
  [(reg-set R reg-i a_2 R_2)
   ----- "Step-Phi-Value-First"
   (--> p R ((reg-i = phi t [a_2 lbl-i] [a-or-r lbl-i_2]) l_2) lbl-i c R_2 l_2 lbl-i c)]
  ; Lookup second input register in the register file, set reg-i if label matches
  [(reg-lookup R reg-i_2 a_2)
   (reg-set R reg-i a_2 R_2)
   ----- "Step-Phi-Reg-Second"
   (--> p R ((reg-i = phi t [a-or-r lbl-i] [reg-i_2 lbl-i_2]) l_2) lbl-i_2 c R_2 l_2 lbl-i_2 c)]
  ; Set reg-i to the second value if label matches
  [(reg-set R reg-i a_2 R_2)
   ----- "Step-Phi-Value-Second"
   (--> p R ((reg-i = phi t [a-or-r lbl-i] [a_2 lbl-i_2]) l_2) lbl-i_2 c R_2 l_2 lbl-i_2 c)]
  ; Set reg-i to 1 if reg-i_1 < reg-i_2
  [(reg-lookup R reg-i_1 a_2)
   (reg-lookup R reg-i_2 a_3)
   (reg-set R reg-i 1 R_2)
   (where #t (lesser a_2 a_3))
   ----- "ICMP-Less"
   (--> p R ((reg-i = icmp slt t reg-i_1 reg-i_2) l_2) c c_1 R_2 l_2 c c_1)]
  ; Set reg-i to 0 if reg-i_1 >= reg-i_2
  [(reg-lookup R reg-i_1 a_2)
   (reg-lookup R reg-i_2 a_3)
   (reg-set R reg-i 0 R_2)
   (where #f (lesser a_2 a_3))
   ----- "ICMP-NotLess"
   (--> p R ((reg-i = icmp slt t reg-i_1 reg-i_2) l_2) c c_1 R_2 l_2 c c_1)]
  ; Branch to lbl-i and update the previous label to the current one
  [(label-lookup p lbl-i l)
   ----- "Branch"
   (--> p R (br label lbl-i) c c_1 R_2 l c_1 lbl-i)]
  ; Branch if reg-i value is 1 to lbl-i
  [(label-lookup p lbl-i l)
   (reg-lookup R reg-i a_1)
   (where #f (different a_1 1))
   ----- "Branch-i1"
   (--> p R (br i1 reg-i label lbl-i label lbl-i_2) c c_1 R_2 l c_1 lbl-i)]
  ; Branch if reg-i value is 0 to lbl-i_2
  [(label-lookup p lbl-i_2 l)
   (reg-lookup R reg-i a_1)
   (where #t (different a_1 1))
   ----- "Branch-i0"
   (--> p R (br i1 reg-i label lbl-i label lbl-i_2) c c_1 R_2 l c_1 lbl-i_2)]
)

; add evaluation condition
; model verilog
; model compilation
; show something!
