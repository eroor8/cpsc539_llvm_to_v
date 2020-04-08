#lang racket

(require
   "verilog_model.rkt"
   "llvm_model.rkt"
   "expression_evaluation.rkt"
   "assignment_evaluation.rkt"
   "compilation_pass1.rkt"
   "compilation_pass2.rkt"
   racket/match
   redex/reduction-semantics)

; EXAMPLE of compilation from a working LLVM program to 
; a Verilog program with the same output observable.

; pseudocode
; find greatest power of two lower than bound
; example (int bound)
;    i = 1    
;    while (i * 2 < bound)
;        i = i * 2
;    return i

; Original code with one phi instr
(term "Working example (phi only on first line of block)")
(term "Test Starting LLVM observable -> evaluates to 64")
(judgment-holds (eval
     (label entry (br label one)
     (label one ((rv0 = phi i32 [1 entry] [rv1 two])
                ((rmul = mul nsw i32 rv0 2)
                ((rcontinue = icmp sle i32 rmul rbound)
                (br i1 rcontinue label two label three))))
     (label two ((rv1 = mul nsw i32 rv0 2)
                (br label one))
     (label three (ret i32 rv0) empty))))
(empty rbound 89) 64))
 
(term "Do pass 1")
(judgment-holds (-->pass1
     (label entry (br label one)
     (label one ((rv0 = phi i32 [1 entry] [rv1 two])
                ((rmul = mul nsw i32 rv0 2)
                ((rcontinue = icmp sle i32 rmul rbound)
                (br i1 rcontinue label two label three))))
     (label two ((rv1 = mul nsw i32 rv0 2)
                (br label one))
     (label three (ret i32 rv0) empty))))
     
     (label entry (br label one)
     (label one ((rv0 = phi i32 (1 entry) (rv1 5)) (br label 1))
     (label 1 ((rmul = mul nsw i32 rv0 2) (br label 2))
     (label 2 ((rcontinue = icmp sle i32 rmul rbound) (br label 3))
     (label 3 (br i1 rcontinue label two label three)
     (label two ((rv1 = mul nsw i32 rv0 2) (br label 5))
     (label 5 (br label one) (label three (ret i32 rv0) empty))))))))
))

(term "Do pass 2 with output of pass 1")
(judgment-holds (-->pass2
     (label entry (br label one)
     (label one ((rv0 = phi i32 (1 entry) (rv1 5)) (br label 1))
     (label 1 ((rmul = mul nsw i32 rv0 2) (br label 2))
     (label 2 ((rcontinue = icmp sle i32 rmul rbound) (br label 3))
     (label 3 (br i1 rcontinue label two label three)
     (label two ((rv1 = mul nsw i32 rv0 2) (br label 5))
     (label 5 (br label one) (label three (ret i32 rv0) empty))))))))

  (empty rbound 89)

(mod
   (always-comb begincase nextstate empty endcase)
   (always-sync
    begincase
    nextstate
    ((((((((empty three ((finished <= 1) ((result-reg <= rv0) end)))
           5
           ((laststate <= nextstate) ((nextstate <= one) end)))
          two
          ((rv1 <= (rv0 * 2))
           ((laststate <= nextstate) ((nextstate <= 5) end))))
         3
         ((laststate <= nextstate)
          ((nextstate <= ((rcontinue == 1) ? two : three)) end)))
        2
        ((rcontinue <= (~ (rmul > rbound)))
         ((laststate <= nextstate) ((nextstate <= 3) end))))
       1
       ((rmul <= (rv0 * 2)) ((laststate <= nextstate) ((nextstate <= 2) end))))
      one
      ((rv0 <= ((laststate == entry) ? 1 : ((laststate == 5) ? rv1 : X)))
       ((laststate <= nextstate) ((nextstate <= 1) end))))
     entry
     ((laststate <= nextstate) ((nextstate <= one) end)))
    endcase)
   endmodule)

(((((((((empty rbound 89) rv0 X) rmul X) rcontinue X) rv1 X) laststate X)
     nextstate
     entry)
    result-reg
    X)
   finished
   0)
))

(term "Run output of pass 2 -> evaluates to 64!")
(judgment-holds (run-v
   (((((((((empty rbound 89) rv0 X) rmul X) rcontinue X) rv1 X) laststate X) nextstate 55) result-reg X) finished 0)
                 empty
                 (mod
   (always-comb begincase nextstate empty endcase)
   (always-sync
    begincase
    nextstate
    ((((((((empty three ((finished <= 1) ((result-reg <= rv0) end)))
           5
           ((laststate <= nextstate) ((nextstate <= one) end)))
          two
          ((rv1 <= (rv0 * 2))
           ((laststate <= nextstate) ((nextstate <= 5) end))))
         3
         ((laststate <= nextstate)
          ((nextstate <= ((rcontinue == 1) ? two : three)) end)))
        2
        ((rcontinue <= (~ (rmul > rbound)))
         ((laststate <= nextstate) ((nextstate <= 3) end))))
       1
       ((rmul <= (rv0 * 2)) ((laststate <= nextstate) ((nextstate <= 2) end))))
      one
       ((rv0 <= ((laststate == 55) ? 1 : ((laststate == 5) ? rv1 : X)))
       ((laststate <= nextstate) ((nextstate <= 1) end))))
     55
     ((laststate <= nextstate) ((nextstate <= one) end)))
    endcase)
   endmodule)
                 a ) a)

(term "Counter-example (multiply phis per block)")
(term "Test Starting LLVM observable -> 2^4 evaluates to 16")
; Original code with two phi instrs
(judgment-holds (eval
    (label entry (br label one)
    (label one ((rv = phi i32 [1 entry] [rfour two])
               ((ri = phi i32 [1 entry] [rfive two])
               ((rcontinue = icmp sle i32 ri rpower)
               (br i1 rcontinue label two label three))))
    (label two ((rfour = mul nsw i32 rv 2)
               ((rfive = add nsw i32 ri 1)
               (br label one)))
    (label three (ret i32 rv) empty)))) (empty rpower 4) 16))

(term "Do pass 1")
(judgment-holds (-->pass1
    (label entry (br label one)
    (label one ((rv = phi i32 [1 entry] [rfour two])
               ((ri = phi i32 [1 entry] [rfive two])
               ((rcontinue = icmp sle i32 ri rpower)
               (br i1 rcontinue label two label three))))
    (label two ((rfour = mul nsw i32 rv 2)
               ((rfive = add nsw i32 ri 1)
               (br label one)))
    (label three (ret i32 rv) empty))))
     
    (label entry (br label one)
    (label one ((rv = phi i32 (1 entry) (rfour 6)) (br label 1))
    (label 1 ((ri = phi i32 (1 entry) (rfive 6)) (br label 2))
    (label 2 ((rcontinue = icmp sle i32 ri rpower) (br label 3))
    (label 3 (br i1 rcontinue label two label three)
    (label two ((rfour = mul nsw i32 rv 2) (br label 5))
    (label 5 ((rfive = add nsw i32 ri 1) (br label 6))
    (label 6 (br label one)
    (label three (ret i32 rv) empty)))))))))
))

(term "Run output of pass 2 : fails because phis are not in original blocks")
(judgment-holds (eval
    (label entry (br label one)
    (label one ((rv = phi i32 (1 entry) (rfour 6)) (br label 1))
    (label 1 ((ri = phi i32 (1 entry) (rfive 6)) (br label 2))
    (label 2 ((rcontinue = icmp sle i32 ri rpower) (br label 3))
    (label 3 (br i1 rcontinue label two label three)
    (label two ((rfour = mul nsw i32 rv 2) (br label 5))
    (label 5 ((rfive = add nsw i32 ri 1) (br label 6))
    (label 6 (br label one)
    (label three (ret i32 rv) empty)))))))))
     (empty rpower 4) a) a)



;; Proofs of full program correctness

;; PASS 1
;; We want to prove that taking a single step in the source program is equivalent to
;; taking some number of steps in the destination program.
;;  src program p compiles to dest program p_2
;;  executing some instruction in p outputs register file R_11 and jumps to a new instruction
;;  executing the equivalent instruction in p_2 outputs same register file, jumps to same new instruction
;; This assumes that the previous label pointer is the same for the compiled instruction though,
;; which isn't necessarily the case. Only phi uses this value however.


(define-judgment-form  MyLLVM
  ; Step until we reach return
  ; p c R -> a
  ; Where p is the program, c is the starting label and
  ; R are the input registers
  #:contract (same-results         integer lbl-i p R  c c c c any)
  #:mode     (same-results         I       I     I I  I I I I O)
  [(-->pass1a integer_0 p p_2 lbl-list)     ; If compilation transforms p to p2
   (label-lookup p lbl-i l)                             ; and instruction l is changed to l_2
   (label-lookup p_2 lbl-i l_2)                             ; and instruction l is changed to l_2
   ; Executing instruction l produces new register file R_11 and jumps to instr l-br at label c_13
   (-->l p R l   c_10 c_11 R_11 l-br   c_12 c_13)  
   ; Executing instruction l_2 produces the same register file and also jumps to instr l-br at label c_13
   (-->l+ p_2 R l_2 c_14 c_15 R_21 l-br_2 c_22 c_23)  ;
   (where #f (differentl R_11 R_21))                        ; the reg file is the same after
   (where #f (differentl l-br l-br_2))                      ; they jump to the same instruction
   ------------------------------ "SameBr"
   
   (same-results integer_0 lbl-i p R c_10 c_11 c_14 c_15 1)]
  [(-->pass1a integer_0 p p_2 lbl-list)     ; If compilation transforms p to p2
   (label-lookup p lbl-i l)                             ; and instruction l is changed to l_2
   (label-lookup p_2 lbl-i l_2)                             ; and instruction l is changed to l_2
   ; Executing instruction l produces new register file R_11 and jumps to instr l-br at label c_13
   (-->l p R l   c_10 c_11 R_11 (l_2 l_3)   c_12 c_13)  
   ; Executing instruction l_2 produces the same register file and also jumps to instr l-br at label c_13
   (-->l+ p_2               R l_2 c_14 c_15 R_21 (l_4 l_5) c_22 c_23)  ;
   (where #f (differentl R_11 R_21))                    ; the reg file is the same after
   (where #f (differentl l_4 l_2))                      ; they jump to the same instruction
   ------------------------------ "SameNb"
   (same-results integer_0 lbl-i p R c_10 c_11 c_14 c_15 1)]

  )

; Example : branch instruction
(judgment-holds (-->l (label 0 (br label 0) empty) (empty rd 1) (br label 0) 0 0 (empty rd 1) (br label 0) 0 0))
(judgment-holds (-->pass1a 9 (label testlabel (br label testlabel) empty)
                             (label testlabel (br label testlabel) empty) empty))
(judgment-holds (label-lookup (label testlabel (br label testlabel) empty) testlabel (br label testlabel)))
(judgment-holds (same-results 9 0 (label 0 (br label 4) (label 4 (br label ten) empty)) (empty rd 1) 2 3 4 5 1))
;(build-derivations (same-results 9 (label testlabel (br label testlabel) empty) (empty rd 1) 0 0 1))

; Example : mul instruction
(judgment-holds (-->pass1a 9
      (label 0 ((rd = mul nsw i32 rd 2) (br label missing)) empty)
      (label 0 ((rd = mul nsw i32 rd 2) (br label 9))(label 9 (br label missing) empty))
      (empty 0 9)))
(judgment-holds (label-lookup
                 (label 0 ((rd = mul nsw i32 rd 2) (br label missing)) empty)
                 0 ((rd = mul nsw i32 rd 2) (br label missing))))
(judgment-holds (label-lookup
                 (label 0 ((rd = mul nsw i32 rd 2) (br label 9))(label 9 (br label missing) empty))
                 0 ((rd = mul nsw i32 rd 2) (br label 9))))

(judgment-holds (-->l
                 (label 0 ((rd = mul nsw i32 rd 2) (br label missing)) empty)
                 (empty rd 1)
                 ((rd = mul nsw i32 rd 2) (br label missing))
                 0 0 (empty rd 2) (br label missing) 0 0))

(judgment-holds (-->l+
                 (label 0 ((rd = mul nsw i32 rd 2) (br label 9))(label 9 (br label missing) empty))
                 (empty rd 1)
                 ((rd = mul nsw i32 rd 2) (br label 9))
                 0 0 (empty rd 2) (br label missing) 0 9))
(judgment-holds (same-results 9 0
     (label 0 ((rd = mul nsw i32 rd 2) (br label missing)) empty)         
     (empty rd 1) 2 3 4 5 1))

;(build-derivations (same-results 9 0
 ;    (label 0 ((rd = mul nsw i32 rd 2) (br label missing)) empty)         
  ;                            (empty rd 1) 0 0 1))
