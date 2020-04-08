#lang racket
(require
   "llvm_model.rkt"
   "verilog_model.rkt"
   "compilation_pass2.rkt"
   racket/match
   redex/reduction-semantics)
(provide (all-defined-out))

(term "Test blocking assignment translation")
(judgment-holds (translate-instr empty ((aa = phi i32 [7 bb] [dd cc]) (br label mylabel))
                                 ((aa <= ((laststate == bb) ? 7 : ((laststate == cc) ? dd : X)))
   ((laststate <= nextstate) ((nextstate <= mylabel) end))) (empty aa X)))
(judgment-holds (translate-instr empty (br label mylabel) ((laststate <= nextstate) ((nextstate <= mylabel) end)) empty)) 
(judgment-holds (translate-instr empty (br i1 reg-test label aa label bb) ((laststate <= nextstate) 
                                 ((nextstate <= ((reg-test == 1) ? aa : bb))  end)) empty))
(judgment-holds (translate-instr empty (ret i32 some-reg)
                                 ((finished <= 1) ((result-reg <= some-reg) end)) empty))  

(judgment-holds (translate-instr empty ((aa = icmp sle i32 bb cc) (br label mylabel))
                                 ((aa <= (~ (bb > cc)))
   ((laststate <= nextstate) ((nextstate <= mylabel) end))) (empty aa X)))
(judgment-holds (translate-instr empty ((aa = mul nsw i32 bb 3) (br label mylabel))
                                 ((aa <= (bb * 3)) ((laststate <= nextstate) ((nextstate <= mylabel) end))) (empty aa X)))
(judgment-holds (translate-instr empty ((aa = add nsw i32 bb 3) (br label mylabel))
                                 ((aa <= (bb + 3)) ((laststate <= nextstate) ((nextstate <= mylabel) end))) (empty aa X)) )

(term "Test whole program translation to blocking")
(judgment-holds (translate-case empty empty empty empty))
(judgment-holds (translate-case empty (label 0 (br label 1)
     (label 1 ((rv = phi i32 [1 entry] [rfour 2]) ((ri = phi i32 [1 entry] [rfive 2]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label 3))))
     (label 2 ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label 1)))
            (label 3 (ret i32 rv) empty))))

    ((((empty 3 ((finished <= 1) ((result-reg <= rv) end)))
     2
     ((rfour <= (rv * 2))
      ((rfive <= (ri + 1)) ((laststate <= nextstate) ((nextstate <= 1) end)))))
    1
    ((rv <= ((laststate == entry) ? 1 : ((laststate == 2) ? rfour : X)))
     ((ri <= ((laststate == entry) ? 1 : ((laststate == 2) ? rfive : X)))
      ((rtwo <= (~ (ri > rd)))
       ((laststate <= nextstate)
        ((nextstate <= ((rtwo == 1) ? two : 3)) end))))))
   0
   ((laststate <= nextstate) ((nextstate <= 1) end)))
    (((((empty rtwo X) ri X) rv X) rfive X) rfour X)))

(term "Test whole program translation to whole program")
(judgment-holds (-->pass2
    (label 0 (br label 1)
     (label 1 ((rv = phi i32 [1 entry] [rfour 2]) ((ri = phi i32 [1 entry] [rfive 2]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label 3))))
     (label 2 ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label 1)))
            (label 3 (ret i32 rv) empty))))
    empty
    (mod
   (always-comb begincase nextstate empty endcase)
   (always-sync
    begincase
    nextstate
    ((((empty 3 ((finished <= 1) ((result-reg <= rv) end)))
       2
       ((rfour <= (rv * 2))
        ((rfive <= (ri + 1))
         ((laststate <= nextstate) ((nextstate <= 1) end)))))
      1
      ((rv <= ((laststate == entry) ? 1 : ((laststate == 2) ? rfour : X)))
       ((ri <= ((laststate == entry) ? 1 : ((laststate == 2) ? rfive : X)))
        ((rtwo <= (~ (ri > rd)))
         ((laststate <= nextstate)
          ((nextstate <= ((rtwo == 1) ? two : 3)) end))))))
     0
     ((laststate <= nextstate) ((nextstate <= 1) end)))
    endcase)
   endmodule)
    (((((((((empty rtwo X) ri X) rv X) rfive X) rfour X) laststate X)
     nextstate
     entry)
    result-reg
    X)
   finished
   0) ))


