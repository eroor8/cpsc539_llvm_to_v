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
  [a ::= integer UNDEFINED]
  ; Indexes: mapping to register values, labels
  [reg-i ::= variable-not-otherwise-mentioned]   
  [lbl-i ::= variable-not-otherwise-mentioned]
  ; Register file: maps register indexes to values
  [R ::= empty                                 
     (R reg-i a)]
  ; Instructions:
  [l ::=
     (br label lbl-i)                      ; branch to label 'lbl-i'
     (reg-i = icmp sle t reg-i reg-i)      ; set reg-i0 to 1 if reg-i1 < reg-i2
     (br i1 reg-i label lbl-i label lbl-i) ; if reg-i is 1, branch to lbl-i0 else lbl-i1
     (reg-i = mul nsw t reg-i a)           ; set reg-i to reg-i * a (of type t)
     (reg-i = add nsw t reg-i a)           ; set reg-i to reg-i + a (of type t)
     ; If the last label was lbl-i0, set reg-i to a-or-r0, else a-or-r1
     (reg-i = phi t [a-or-r lbl-i] [a-or-r lbl-i])
     (ret t reg-i)                       ; return reg-i
     (l l)                                 ; l is a sequence of instructions
     UNDEFINED
     ]  
  ; p is the program: a sequence of labels followed by sequences of instructions
  [p ::= empty (label lbl-i l p)]
  [c ::= lbl-i]
)

; Define some metafunctions to be used during instruction step judgments
(define-metafunction MyLLVM    ; define not equal
  different : any any -> any
  [(different any_1 any_2) ,(not (equal? (term any_1) (term any_2)))])
(define-metafunction MyLLVM    ; define less than
  lesser : any any -> any
  [(lesser any_1 any_2) ,(not (> (term any_1) (term any_2)))])
(define-metafunction MyLLVM    ; define multiplication
  multiply : any any -> any
  [(multiply any_1 any_2) , (* (term any_1) (term any_2))])
(define-metafunction MyLLVM    ; define addition
  addi : any any -> any
  [(addi any_1 any_2) , (+ (term any_1) (term any_2))])

; Test metafunctions
(term (different (term 0) (term 1)))
(not (term (different (term 0) (term 0))))
(term (lesser 0 1))
(term (lesser 1 1))
(equal? (term (multiply 2 10)) 20)
(not (equal? (term (multiply 2 10)) 1))
(equal? (term (addi 2 10)) 12)
(not (equal? (term (add 2 10)) 10))

; Lookup reg-i index to find corresponding value
(define-judgment-form MyLLVM
  #:contract (reg-lookup R reg-i a)
  #:mode (reg-lookup I I O)
  ; Matching key is last pair
  [----- "Lookup-Reg-Last"
   (reg-lookup (R reg-i a) reg-i a)]
  ; Matching key is not last pair
  [(reg-lookup R reg-i_2 a_2)
   (where #t (different a_2 UNDEFINED))
   ----- "Lookup-Reg-NotLast"
   (reg-lookup (R reg-i_1 a_1) reg-i_2 a_2)]
  ; Matching key is not in empty dict
  [
   ----- "Lookup-Reg-Empty"
   (reg-lookup empty reg-i UNDEFINED)]
  [(reg-lookup R reg-i UNDEFINED)
   (where #t (different reg-i reg-i_2))
   ----- "Lookup-Reg-Not-Found"
   (reg-lookup (R reg-i_2 a) reg-i UNDEFINED)]
   )

(judgment-holds (reg-lookup ((empty j 10) t 9) j 10)) ; Lookup-Reg-Last
(judgment-holds (reg-lookup ((empty j 10) t 9) t 9)) ; Lookup-Reg-NotLast
(judgment-holds (reg-lookup empty t UNDEFINED)) ; Lookup-Reg-Empty
(judgment-holds (reg-lookup (empty j 10) t UNDEFINED)) ; Lookup-Reg-Not-Found
 
; Set register reg-i to value a in new register file
(define-judgment-form  MyLLVM
  #:contract (reg-set R reg-i a R)
  #:mode (reg-set I I I O)
  ; Replace existing key
  [
   ----- "Set-Reg-Existing"
   (reg-set (R reg-i a) reg-i a_2 (R reg-i a_2))]
  [(reg-lookup R reg-i_2 a_4)
   (where #t (different a_4 UNDEFINED))
   (where #t (different reg-i reg-i_2))
   (reg-set R reg-i_2 a_2 R_2)
   ----- "Set-Reg-Existing-Inner"
   (reg-set (R reg-i a) reg-i_2 a_2 (R_2 reg-i a))]
  ; Add new key
  [(reg-lookup R reg-i UNDEFINED)
   ----- "Set-Reg-New"
   (reg-set R reg-i a (R reg-i a))]
)
 
; For some reason, doesn't work with moded judgment... hmmm...
(judgment-holds (reg-set (empty t 9) t 10 R) R)       ; Existing > (empty t 9) 
(judgment-holds (reg-set ((empty t 9) j 10) t 10 R) R) ; Inner > ((empty t 10) j 10)
(judgment-holds (reg-set (empty j 9) t 10 R) R) ; New > ((empty j 9) t 10) 

(define-judgment-form  MyLLVM
  #:contract (label-lookup p lbl-i l)
  #:mode (label-lookup I I O)
  ; Find section of program corresponding to lbl-i
  [----- "Lookup-Label-First"
   (label-lookup (label lbl-i l p) lbl-i l)]
  [(label-lookup p lbl-i_2 l_2)
   (where #t (different l_2 UNDEFINED))
   ----- "Lookup-Label-NotFirst"
   (label-lookup (label lbl-i l p) lbl-i_2 l_2)]
 ; Matching key is not in empty dict
  [
   ----- "Lookup-Label-Empty"
   (label-lookup empty lbl-i UNDEFINED)]
  [(label-lookup p lbl-i UNDEFINED)
   (where #t (different lbl-i lbl-i_2))
   ----- "Lookup-Label-Not-Found"
   (label-lookup (label lbl-i_2 l p) lbl-i UNDEFINED)]
  )

; Test looking up labels
(judgment-holds (label-lookup (label kra (br label fr) (label fr (br label kra) empty)) kra (br label fr))) ; first
(judgment-holds (label-lookup (label kra (br label fr) (label fr (br label kra) empty)) fr (br label kra))) ; second
(judgment-holds (label-lookup empty fr UNDEFINED)) ; empty
(judgment-holds (label-lookup (label kra (br label fr) empty) fr UNDEFINED)) ; second

(define-judgment-form  MyLLVM
  ; Step one instruction
  ; p (R l c c) -> (R l c c)
  ; Where R is the register file, p is the program,
  ; l is the current instruction, first c is the previous label
  ; second c is the current label
  #:contract (--> p R l c c R l c c)
  #:mode     (--> I I I I I O O O O)
  ; Lookup input register in the register file, multiply by the value, set reg-i
  [(reg-lookup R reg-i_2 a_2)
   (reg-set R reg-i (multiply a_2 a_1) R_2) 
   ----- "Step-Mul"
   (--> p R ((reg-i = mul nsw t reg-i_2 a_1) l_2) c c_1 R_2 l_2 c c_1)]
  ; Lookup input register in the register file, add to the value, set reg-i
  [(reg-lookup R reg-i_2 a_2)
   (reg-set R reg-i (addi a_2 a_1) R_2) 
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
   (--> p R ((reg-i = icmp sle t reg-i_1 reg-i_2) l_2) c c_1 R_2 l_2 c c_1)]
  ; Set reg-i to 0 if reg-i_1 >= reg-i_2
  [(reg-lookup R reg-i_1 a_2)
   (reg-lookup R reg-i_2 a_3)
   (reg-set R reg-i 0 R_2)
   (where #f (lesser a_2 a_3))
   ----- "ICMP-NotLess"
   (--> p R ((reg-i = icmp sle t reg-i_1 reg-i_2) l_2) c c_1 R_2 l_2 c c_1)]
  ; Branch to lbl-i and update the previous label to the current one
  [(label-lookup p lbl-i l)
   ----- "Branch"
   (--> p R (br label lbl-i) c c_1 R l c_1 lbl-i)]
  ; Branch if reg-i value is 1 to lbl-i
  [(label-lookup p lbl-i l)
   (reg-lookup R reg-i a_1)
   (where #f (different a_1 1))
   ----- "Branch-i1"
   (--> p R (br i1 reg-i label lbl-i label lbl-i_2) c c_1 R l c_1 lbl-i)]
  ; Branch if reg-i value is not 1 to lbl-i_2
  [(label-lookup p lbl-i_2 l)
   (reg-lookup R reg-i a_1)
   (where #t (different a_1 1))
   ----- "Branch-i0"
   (--> p R (br i1 reg-i label lbl-i label lbl-i_2) c c_1 R l c_1 lbl-i_2)]
)

(judgment-holds (--> (label k (br label k) empty) (empty g 4) ((f = mul nsw i32 g 5) (br label k)) k k ((empty g 4) f 20) (br label k) k k)) ; Step-Mul
(judgment-holds (--> (label k (br label k) empty) (empty g 4) ((f = add nsw i32 g 5) (br label k)) k k ((empty g 4) f 9) (br label k) k k)) ; Step-Add
(judgment-holds (--> (label k (br label k) empty) (empty g 4) ((m = phi i32 [g k] [8 n]) (br label k)) k k ((empty g 4) m 4) (br label k) k k)) ; Set-Phi-Reg-First
(judgment-holds (--> (label k (br label k) empty) (empty g 4) ((m = phi i32 [0 k] [8 n]) (br label k)) k k ((empty g 4) m 0) (br label k) k k)) ; Set-Phi-Value-First
(judgment-holds (--> (label k (br label k) empty) (empty g 2) ((m = phi i32 [0 k] [g n]) (br label k)) n k ((empty g 2) m 2) (br label k) n k)) ; Set-Phi-Reg-Second
(judgment-holds (--> (label k (br label k) empty) (empty g 4) ((m = phi i32 [0 k] [8 n]) (br label k)) n k ((empty g 4) m 8) (br label k) n k)) ; Set-Phi-Value-Second
(judgment-holds (--> (label k (br label k) empty) ((empty g 4) j 9) ((m = icmp sle i32 g j) (br label k)) n k (((empty g 4) j 9) m 1) (br label k) n k)) ; ICMP-Less
(judgment-holds (--> (label k (br label k) empty) (empty g 4) ((m = icmp sle i32 g g) (br label k)) n k ((empty g 4) m 0) (br label k) n k)) ; ICMP-Not-Less
(judgment-holds (--> (label kr (br label fr) empty) (empty g 4) (br label kr) kr fr (empty g 4) (br label fr) fr kr)) ; Branch
(judgment-holds (--> (label kr (br label fr) (label fr (br label kr) empty)) (empty g 1) (br i1 g label kr label fr) kr fr (empty g 1) (br label fr) fr kr)) ; Br-i1
(judgment-holds (--> (label kr (br label fr) (label fr (br label kr) empty)) (empty g 4) (br i1 g label kr label fr) kr fr (empty g 4) (br label kr) fr fr)) ; Br-i0

(define-judgment-form  MyLLVM
  ; Step many times
  ; p c R -> a
  ; Where p is the program, c is the starting label and
  ; R are the input registers
  #:contract (run p R l c c R l c c)
  #:mode     (run I I I I I O O O O)
  [(--> p R l c_0 c_1 R_10 l_10 c_10 c_11)
   (run p R_10 l_10 c_10 c_11 R_2 l_2 c_2 c_3)
   ----- "Run"
   (run p R l c_0 c_1 R_2 l_2 c_2 c_3)]
  [(--> p R l c_0 c_1 R_2 l_2 c_2 c_3)
   ----- "Run-Single"
   (run p R l c_0 c_1 R_2 l_2 c_2 c_3)]
  )

(judgment-holds (run (label main ((g = add nsw i32 g 1) (ret i32 g)) empty) (empty g 5) ((g = add nsw i32 g 1) (ret i32 g)) main main (empty g 6) (ret i32 g) main main))
(judgment-holds (run (label main ((g = add nsw i32 g 1) ((g = mul nsw i32 g 2) (ret i32 g))) empty) (empty g 5) ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) main main (empty g 6) ((g = add nsw i32 g 1) (ret i32 g)) main main))
(judgment-holds (run (label main ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) empty) (empty g 5) ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) main main (empty g 7) (ret i32 g) main main))
(judgment-holds (run (label main ((g = add nsw i32 g 1) ((g = mul nsw i32 g 2) (ret i32 g))) empty) (empty g 5) ((g = add nsw i32 g 1) ((g = mul nsw i32 g 2) (ret i32 g))) main main (empty g 12) (ret i32 g) main main))

(define-judgment-form  MyLLVM
  ; Step until we reach return
  ; p c R -> a
  ; Where p is the program, c is the starting label and
  ; R are the input registers
  #:contract (eval p R a)
  #:mode     (eval I I O)
  ; (ret t reg-i)
  [(label-lookup p main l)
   (run p R l main main R_2 (ret i32 reg-i) c_0 c_1)
   (reg-lookup R_2 reg-i a)
   ----- "Step-Mul"
   (eval p R a)]
)

(judgment-holds (eval (label main ((g = add nsw i32 g 1) (ret i32 g)) empty) (empty g 5) 6))
(judgment-holds (eval (label main ((g = add nsw i32 g 1) ((g = mul nsw i32 g 2) (ret i32 g))) empty) (empty g 5) 12))

;Example: Compute 2^rd 
(judgment-holds (eval (label main (br label one) (label one ((rv = phi i32 [1 main] [rfour two]) ((ri = phi i32 [1 main] [rfive two]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three)))) (label two ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label one))) (label three (ret i32 rv) empty)))) (empty rd 5) 32))

(judgment-holds (eval (label main (br label one) (label one ((rv = phi i32 [1 main] [rfour two]) ((ri = phi i32 [1 main] [rfive two]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three)))) (label two ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label one))) (label three (ret i32 rv) empty)))) (empty rd 1) 2))
