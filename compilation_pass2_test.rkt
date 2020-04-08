#lang racket
(require
   "llvm_model.rkt"
   "verilog_model.rkt"
   "compilation_pass2.rkt"
   racket/match
   redex/reduction-semantics)
(provide (all-defined-out))

(term "Test blocking assignment translation")
(judgment-holds (translate-instr ((aa = phi i32 [7 bb] [dd cc]) (br label mylabel))
                                 ((aa <= ((laststate == bb) ? 7 : ((laststate == cc) ? dd : X))) ((laststate <= nextstate) (nextstate <= mylabel)))))
(judgment-holds (translate-instr (br label mylabel) ((laststate <= nextstate) (nextstate <= mylabel)))) 
(judgment-holds (translate-instr (br i1 reg-test label aa label bb) ((laststate <= nextstate) 
                                 (nextstate <= ((reg-test == 1) ? aa : bb)))))
(judgment-holds (translate-instr (ret i32 some-reg)
                                 ((finished <= 1) (result-reg <= some-reg))))  


(judgment-holds (translate-instr ((aa = icmp sle i32 bb cc) (br label mylabel))
                                 ((aa <= (~ (bb > cc))) ((laststate <= nextstate) (nextstate <= mylabel)))))
(judgment-holds (translate-instr ((aa = mul nsw i32 bb 3) (br label mylabel))
                                 ((aa <= (bb * 3)) ((laststate <= nextstate) (nextstate <= mylabel)))))
(judgment-holds (translate-instr ((aa = add nsw i32 bb 3) (br label mylabel))
                                 ((aa <= (bb + 3)) ((laststate <= nextstate) (nextstate <= mylabel)))))

(term "Test whole program translation to blocking")
(judgment-holds (translate-case empty empty))
(judgment-holds (translate-case (label 0 (br label 1)
     (label 1 ((rv = phi i32 [1 entry] [rfour 2]) ((ri = phi i32 [1 entry] [rfive 2]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label 3))))
     (label 2 ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label 1)))
            (label 3 (ret i32 rv) empty))))

    ((((empty
      3 ((finished <= 1) (result-reg <= rv)))
      2 ((rfour <= (rv * 2)) ((rfive <= (ri + 1)) ((laststate <= nextstate) (nextstate <= 1)))))
      1 ((rv <= ((laststate == entry) ? 1 : ((laststate == 2) ? rfour : X)))
        ((ri <= ((laststate == entry) ? 1 : ((laststate == 2) ? rfive : X)))
        ((rtwo <= (~ (ri > rd)))((laststate <= nextstate) (nextstate <= ((rtwo == 1) ? two : 3)))))))
      0
        ((laststate <= nextstate) (nextstate <= 1)))))

(term "Test whole program translation to whole program")
(judgment-holds (translate-program
    (label 0 (br label 1)
     (label 1 ((rv = phi i32 [1 entry] [rfour 2]) ((ri = phi i32 [1 entry] [rfive 2]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label 3))))
     (label 2 ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label 1)))
            (label 3 (ret i32 rv) empty))))

    (mod
   (always-sync
    begincase
    nextstate
    ((((empty 3 ((finished <= 1) (result-reg <= rv)))
       2
       ((rfour <= (rv * 2))
        ((rfive <= (ri + 1)) ((laststate <= nextstate) (nextstate <= 1)))))
      1
      ((rv <= ((laststate == entry) ? 1 : ((laststate == 2) ? rfour : X)))
       ((ri <= ((laststate == entry) ? 1 : ((laststate == 2) ? rfive : X)))
        ((rtwo <= (~ (ri > rd)))
         ((laststate <= nextstate) (nextstate <= ((rtwo == 1) ? two : 3)))))))
     0
     ((laststate <= nextstate) (nextstate <= 1)))
    endcase)
   endmodule)

    empty))


