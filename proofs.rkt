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





