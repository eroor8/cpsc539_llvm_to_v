#lang racket
(require
   "verilog_model.rkt"
   "expression_evaluation.rkt"
   "assignment_evaluation.rkt"
   racket/match
   redex/reduction-semantics)

; Test metafunctions
(term "Test useful metafunctions")
(term (different (term 0) (term 1)))
(not (term (different (term 0) (term 0))))
(term (same (term 1) (term 1)))
(not (term (same (term 1) (term 0))))
(equal? (term (shift-left 3 0)) 3)
(equal? (term (shift-left 3 2)) 12)
(term (greater 1 0))
(not (term (greater 1 9)))
(term (lesser 0 1))
(not (term (lesser 1 1)))
(equal? (term (multiply 2 10)) 20)
(not (equal? (term (multiply 2 10)) 1))
(equal? (term (addi 2 10)) 12)
(not (equal? (term (add 2 10)) 10))

; Test lookups and sets of registers and wires
(term "Test looking up and settings registers and wires")
(judgment-holds (reg-lookup ((empty j 10) t 9) j 10)) ; Lookup-Reg-Last
(judgment-holds (reg-lookup ((empty j 10) t 9) t 9)) ; Lookup-Reg-NotLast

(judgment-holds (wire-lookup ((empty f X) g (reg-1 + 5)) f X))
(judgment-holds (wire-lookup ((empty f 10) g (reg-1 + 5)) g (reg-1 + 5)))
  
(judgment-holds (reg-set (empty t 9) t 10 (empty t 10)))       ; Existing > (empty t 9) 
(judgment-holds (reg-set ((empty t 9) j 10) t 10 ((empty t 10) j 10))) ; Inner > ((empty t 10) j 10)

(judgment-holds (wire-set (empty wire-1 7) wire-1 (reg-i + 5) (empty wire-1 (reg-i + 5)))) 
(judgment-holds (wire-set ((empty wire-1 7) wire-2 1) wire-1 (reg-1 + (4 + reg-2)) ((empty wire-1 (reg-1 + (4 + reg-2))) wire-2 1))) 
(judgment-holds (wire-set ((empty wire-1 7) wire-2 X) wire-2 (reg-1 + (4 + reg-2)) ((empty wire-1 7) wire-2 (reg-1 + (4 + reg-2))))) 

(judgment-holds (case-lookup
                ((empty f ten) g five)
                ((empty ten end) five (end end))
                g
                (end end)
                ))

;; Test step
(term "Test expression reduction")
(judgment-holds (-->e empty empty (7 == 7) 1)) 
(judgment-holds (-->e empty empty (X == 7) X)) 
(judgment-holds (-->e empty empty (7 == X) X)) 
(judgment-holds (-->e empty empty (X == X) X)) 
(judgment-holds (-->e empty empty (7 == 2) 0)) 
(judgment-holds (-->e empty empty (7 < 10) 1)) 
(judgment-holds (-->e empty empty (X < 7) X)) 
(judgment-holds (-->e empty empty (7 < X) X)) 
(judgment-holds (-->e empty empty (X < X) X)) 
(judgment-holds (-->e empty empty (7 < 7) 0)) 
(judgment-holds (-->e empty empty (7 > 8) 0)) 
(judgment-holds (-->e empty empty (X > 7) X)) 
(judgment-holds (-->e empty empty (7 > X) X))
(judgment-holds (-->e empty empty (X > X) X)) 
(judgment-holds (-->e empty empty (7 > 2) 1))
(judgment-holds (-->e empty empty (X * 7) X)) 
(judgment-holds (-->e empty empty (7 * X) X)) 
(judgment-holds (-->e empty empty (X * X) X)) 
(judgment-holds (-->e empty empty (7 * 2) 14))
(judgment-holds (-->e empty empty (7 * 0) 0))
(judgment-holds (-->e empty empty (X + 7) X)) 
(judgment-holds (-->e empty empty (7 + X) X)) 
(judgment-holds (-->e empty empty (X + X) X)) 
(judgment-holds (-->e empty empty (7 + 2) 9))
(judgment-holds (-->e empty empty (7 + 0) 7))
(judgment-holds (-->e empty empty (X - 7) X)) 
(judgment-holds (-->e empty empty (7 - X) X)) 
(judgment-holds (-->e empty empty (0 - 2) -2))
(judgment-holds (-->e empty empty (7 - 2) 5))
(judgment-holds (-->e empty empty (X <<< 7) X)) 
(judgment-holds (-->e empty empty (7 <<< X) X)) 
(judgment-holds (-->e empty empty (X <<< X) X)) 
(judgment-holds (-->e empty empty (8 <<< 2) 32))
(judgment-holds (-->e empty empty (7 <<< 0) 7))
(judgment-holds (-->e empty empty (~ X) X)) 
(judgment-holds (-->e empty empty (~ 0) 1))
(judgment-holds (-->e empty empty (~ 7) 0))
(judgment-holds (-->e empty empty (X && 7) X)) 
(judgment-holds (-->e empty empty (7 && X) X)) 
(judgment-holds (-->e empty empty (X && X) X))
(judgment-holds (-->e empty empty (0 && X) 0))
(judgment-holds (-->e empty empty (X && 0) 0)) 
(judgment-holds (-->e empty empty (8 && 2) 1))
(judgment-holds (-->e empty empty (1 && 0) 0))
(judgment-holds (-->e empty empty (0 && 1) 0))
(judgment-holds (-->e empty empty (X || 7) 1))
(judgment-holds (-->e empty empty (5 || X) 1))  
(judgment-holds (-->e empty empty (X || 0) X)) 
(judgment-holds (-->e empty empty (X || X) X)) 
(judgment-holds (-->e empty empty (0 || 1) 1))
(judgment-holds (-->e empty empty (7 || 0) 1))
(judgment-holds (-->e empty empty (7 || 1) 1))
(judgment-holds (-->e empty empty (0 || 0) 0))
 
(judgment-holds (-->e empty empty (0 ? 2 : 3) 3))
(judgment-holds (-->e empty empty (1 ? 2 : 3) 2))
(judgment-holds (-->e (empty f 5) empty f 5)) 
(judgment-holds (-->e empty (empty f (reg-i + 3)) f (reg-i + 3))) 

;; Test continuation
(term "Test expression continuation")
(judgment-holds (-->+ empty empty (7 == 1) 0))
(judgment-holds (-->+ empty empty (0 == 0) 1))
(judgment-holds (-->+ empty empty (0 == (1 == 1)) (0 == 1)))
(judgment-holds (-->+ empty empty (0 == (1 == 7)) (0 == 0)))
(judgment-holds (-->+ empty empty (0 < (1 < 2)) (0 < 1)))
(judgment-holds (-->+ empty empty (0 < (1 < 0)) (0 < 0)))
(judgment-holds (-->+ empty empty (1 > (1 > 0)) (1 > 1)))
(judgment-holds (-->+ empty empty (1 > (1 > 7)) (1 > 0)))
(judgment-holds (-->+ empty empty (0 * (1 * 7)) (0 * 7)))
(judgment-holds (-->+ empty empty (2 * (1 * 2)) (2 * 2)))
(judgment-holds (-->+ empty empty (9 - (5 - 1)) (9 - 4)))
(judgment-holds (-->+ empty empty (3 - (2 - 4)) (3 - -2)))
(judgment-holds (-->+ empty empty (0 + (1 + 2)) (0 + 3)))
(judgment-holds (-->+ empty empty (1 + (2 + 4)) (1 + 6)))
(judgment-holds (-->+ empty empty (5 <<< (1 <<< 1)) (5 <<< 2)))
(judgment-holds (-->+ empty empty (1 <<< (3 <<< 0)) (1 <<< 3)))
(judgment-holds (-->+ empty empty (~ (~ 7)) (~ 0)))
(judgment-holds (-->+ empty empty (9 && (1 && 0)) (9 && 0)))
(judgment-holds (-->+ empty empty (1 && (1 && 7)) (1 && 1)))
(judgment-holds (-->+ empty empty ((3 == 2) ? 2 : 3) (0 ? 2 : 3)))

;; Test conversion
(term "Test expression conversion")
(judgment-holds (-->* empty empty (7 == 1) (7 == 1)))
(judgment-holds (-->* empty empty (7 == 1) 0))
(judgment-holds (-->* empty empty (0 == 0) 1))
(judgment-holds (-->* empty empty (0 == (1 == 1)) 0))
(judgment-holds (-->* empty empty (0 == (1 == 7)) 1))
(judgment-holds (-->* empty empty ((1 < 0) < (1 < 2)) 1))
(judgment-holds (-->* empty empty (0 < (1 < 0)) 0))
(judgment-holds (-->* empty empty ((1 > 0) > (1 > 0)) 0))
(judgment-holds (-->* empty empty (1 > (1 > 7)) 1))
(judgment-holds (-->* empty empty ((0 * 8) * (1 * 7)) 0))
(judgment-holds (-->* empty empty (2 * (1 * 2)) 4))
(judgment-holds (-->* empty empty ((8 + 1) - (5 - 1)) 5))
(judgment-holds (-->* empty empty (3 - (2 - 4)) 5))
(judgment-holds (-->* empty empty (0 + (1 + 2)) 3))
(judgment-holds (-->* empty empty (1 + (2 + 4)) 7))
(judgment-holds (-->* empty empty (((1 <<< 1) + 3) <<< (1 <<< 1)) 20))
(judgment-holds (-->* empty empty (1 <<< (3 <<< 0)) 8))
(judgment-holds (-->* empty empty (~ (~ 7)) 1))
(judgment-holds (-->* empty empty (9 && (1 && 0)) 0))
(judgment-holds (-->* empty empty (1 && (1 && 7)) 1))
(judgment-holds (-->* (empty reg-i 7) empty (1 && (1 && reg-i)) 1))
(judgment-holds (-->* empty (empty wire-i 0) (1 && (1 && wire-i)) 0))
(judgment-holds (-->* empty (empty wire-i (1 + 4)) (1 + (2 * wire-i)) 11))
(judgment-holds (-->* empty ((empty wire-i2 (6 - 2)) wire-i (1 + wire-i2)) (1 + (2 * wire-i)) 11))
(judgment-holds (-->* empty empty ((3 == 2) ? 4 : 2) 2))
(judgment-holds (-->* empty empty ((2 == 2) ? 4 : 2) 4))

; Test evaluation of expression
(term "Test expression evaluation")
(judgment-holds (eval-e empty empty (7 == 1) 0))
(judgment-holds (eval-e empty empty (0 == 0) 1))
(judgment-holds (eval-e empty empty (0 == (1 == 1)) 0))
(judgment-holds (eval-e empty empty (0 == (1 == 7)) 1))
(judgment-holds (eval-e empty empty ((1 < 0) < (1 < 2)) 1))
(judgment-holds (eval-e empty empty (0 < (1 < 0)) 0))
(judgment-holds (eval-e empty empty ((1 > 0) > (1 > 0)) 0))
(judgment-holds (eval-e empty empty (1 > (1 > 7)) 1))
(judgment-holds (eval-e empty empty ((0 * 8) * (1 * 7)) 0))
(judgment-holds (eval-e empty empty (2 * (1 * 2)) 4))
(judgment-holds (eval-e empty empty ((8 + 1) - (5 - 1)) 5))
(judgment-holds (eval-e empty empty (3 - (2 - 4)) 5))
(judgment-holds (eval-e empty empty (0 + (1 + 2)) 3))
(judgment-holds (eval-e empty empty (1 + (2 + 4)) 7))
(judgment-holds (eval-e empty empty (((1 <<< 1) + 3) <<< (1 <<< 1)) 20))
(judgment-holds (eval-e empty empty (1 <<< (3 <<< 0)) 8))
(judgment-holds (eval-e empty empty (~ (~ 7)) 1))
(judgment-holds (eval-e empty empty (9 && (1 && 0)) 0))
(judgment-holds (eval-e empty empty (1 && (1 && 7)) 1))
(judgment-holds (eval-e (empty reg-i 7) empty (1 && (1 && reg-i)) 1))
(judgment-holds (eval-e empty (empty wire-i 0) (1 && (1 && wire-i)) 0))
(judgment-holds (eval-e empty (empty wire-i (1 + 4)) (1 + (2 * wire-i)) 11))
(judgment-holds (eval-e empty ((empty wire-i2 (6 - 2)) wire-i (1 + wire-i2)) (1 + (2 * wire-i)) 11))
(judgment-holds (eval-e (empty reg-i 1) empty ((2 == reg-i) ? 4 : 2) 2))
(judgment-holds (eval-e (empty reg-i 2) empty ((2 == reg-i) ? 4 : 2) 4))


; Test doing one blocking instruction
(term "Test blocking assignment")
(judgment-holds (-->b (empty reg-i 7) ((empty wire-2 (reg-i + 1)) wire-i 7) ((wire-2 = 5) (end end)) ((empty wire-2 5) wire-i 7) (end end)))
(judgment-holds (-->b (empty reg-i 7) ((empty wire-2 (reg-i + 1)) wire-i 7) ((wire-2 = 5) ((wire-2 = (reg-i + 3)) end)) ((empty wire-2 5) wire-i 7) ((wire-2 = (reg-i + 3)) end)))
(judgment-holds (-->b (empty reg-i 7) ((empty wire-2 5) wire-i 7) ((wire-i = (reg-i + wire-2)) end) ((empty wire-2 5) wire-i (reg-i + wire-2)) end))

; Test doing one non-blocking instructions
(term "Test non-blocking assignment")
(judgment-holds (-->nb (empty reg-i 7) (empty reg-i 2) (empty wire-2 (reg-i + 1)) ((reg-i <= (wire-2 + 2)) end) (empty reg-i 10) end))
(judgment-holds (-->nb (empty reg-i 7) (empty reg-i 2) (empty wire-2 (reg-i + 1)) ((reg-i <= (wire-2 + 2)) end) (empty reg-i 10) end))
(judgment-holds (-->nb (empty reg-i 7) (empty reg-i 2) (empty wire-2 (reg-i + 1)) ((reg-i <= testlabel) end) (empty reg-i testlabel) end))

; Test evaluating a set of blocking assingments
(term "Test a set of blocking assignments")
(judgment-holds (eval-b (empty reg-i 7) (empty wire-i 7) end (empty wire-i 7)))
(judgment-holds (eval-b (empty reg-i 7) ((empty wire-2 (reg-i + 1)) wire-i 7) ((wire-2 = 5) ((wire-i = (reg-i + 3)) end)) ((empty wire-2 5) wire-i (reg-i + 3))))
(judgment-holds (eval-b (empty reg-i 7) ((empty wire-2 (reg-i + 1)) wire-i 7) ((wire-2 = 5) ((wire-i = (reg-i + 3)) end)) ((empty wire-2 5) wire-i (reg-i + 3))))

; Test evaluating a set of nonblocking assingments
(term "Test a set of nonblocking assignments")
(judgment-holds (eval-nb
                 (empty reg-i X)
                 (empty reg-i 1)
                 (empty wire-i 7)
                 end
                 (empty reg-i 1)))
(judgment-holds (eval-nb
                 ((empty reg-i 3) reg-t 1)
                 ((empty reg-i 3) reg-t 1)
                 ((empty wire-i (reg-i * 2)) wire-t ((7 - 2) * reg-t))
                 ((reg-t <= (wire-t + reg-t)) ((reg-i <= (wire-i + reg-t)) end))
                 ((empty reg-i 7) reg-t 6)
                 ))

;; Evaluate full always block
(term "Test a combinational always block")
(judgment-holds (eval-always-comb
                 (empty reg-i three)
                 (empty wire-i 1) ; W
                 (always-comb begincase reg-i 
                    (empty three end)
                     endcase)
                 (empty wire-i 1)
                 ))

(judgment-holds (eval-always-comb
                 ((empty reg-i three) reg-m 2) ; R
                 ((empty wire-2 (reg-i + 1)) wire-i 7) ; W
                 
                 (always-comb begincase reg-m 
                              ((empty
                               2
                                  ((wire-2 = 5) (
                                  (wire-i = (reg-i + 3))
                                  end)))
                               three
                                  ((wire-2 = 1) (
                                  (wire-i = 1)
                                  end))
                              )
                     endcase)
                 ((empty wire-2 5) wire-i (reg-i + 3))
                 ))

(term "Test a synchronous always block")
(judgment-holds (eval-always-sync
                 (empty reg-i three)
                 (empty wire-i 1) ; W
                 (always-sync begincase reg-i 
                    (empty three end)
                     endcase)
                 (empty reg-i three)
                 ))

(judgment-holds (eval-always-sync
                 ((empty reg-i three) reg-m 2) ; R
                 ((empty wire-2 (reg-i + 1)) wire-i (reg-m + 2)) ; W
                 
                 (always-sync begincase reg-i
                              ((empty
                               2
                                  ((reg-i <= 5) (
                                  (reg-m <= three)
                                  end)))
                               three
                                  ((reg-i <= (wire-i * 3)) (
                                  (reg-m <= 3)
                                  end))
                              )
                     endcase)
                 ((empty reg-i 12) reg-m 3)
                 ))

(term "Run start to finish!")
(judgment-holds (cycle
                 ((empty reg-i zero) reg-m 0) ; R
                 ((empty wire-i 0) wire-m 0) ; W
                 (always-sync begincase reg-i ;(empty 0 end)
                              ((empty
                               zero
                                  ((reg-i <= 1) (
                                  (reg-m <= 1)
                                  end)))
                               three
                                  ((reg-i <= 2) (
                                  (reg-m <= 2)
                                  end))
                              )
                     endcase)                 
                 (always-comb begincase reg-i ;(empty 0 end)
                              ((empty
                               zero
                                  ((wire-m = 3) (
                                  (wire-i = 3)
                                  end)))
                               three
                                  ((wire-m = 4) (
                                  (wire-i = 4)
                                  end))
                              )
                     endcase)
                 ((empty reg-i 1) reg-m 1)
                 ((empty wire-i 3) wire-m 3) ; W
                 ))

(judgment-holds (cycle
                 ((empty state-reg zero) result-reg 0) ; R
                 (((empty finished 0) start 1) input-wire 4) ; W
                 (always-sync begincase state-reg ;(empty 0 end)
                              ((empty
                               zero
                                  ((result-reg <= (input-wire * 2)) (
                                  (state-reg <= three)
                                  end)))
                               three
                                  ((result-reg <= (result-reg + 3)) (
                                  (state-reg <= three)
                                  end))
                              )
                     endcase)                 
                 (always-comb begincase state-reg ;(empty 0 end)
                              empty
                     endcase)
                 ((empty state-reg three) result-reg 8)                
                 (((empty finished 0) start 1) input-wire 4) ; W
                 ))

(term "Run full program")
(judgment-holds (run-v
                 (((empty finished 0) state-reg zero) result-reg 0) ; R
                 ((empty input-wire 4) start 1) ; W
                 (mod (always-comb begincase state-reg empty endcase)
                      (always-sync begincase state-reg ;(empty 0 end)
                              ((empty
                               zero
                                  ((result-reg <= (input-wire * 2)) (
                                  (state-reg <= donest)
                                  end)))
                               donest
                                  ((result-reg <= result-reg) (
                                  (state-reg <= donest)
                                  ((finished <= 1)
                                  end)))
                              )
                              endcase)
                      endmodule)
                 8 ))

(judgment-holds (run-v
                 (((empty finished 0) state-reg donest) result-reg 8)    
                 ((empty input-wire 4) start 1)
                 (mod                  
                 (always-comb begincase state-reg
                              empty
                              endcase)
                 (always-sync begincase state-reg
                              ((empty
                               0
                                  ((result-reg <= (input-wire * 2)) (
                                  (state-reg <= donest)
                                  end)))
                               donest
                                  ((result-reg <= result-reg)
                                  ((state-reg <= donest)
                                  ((finished <= 1)
                                  end)))
                              )
                              endcase)
                 endmodule)
                 8 ))

(judgment-holds (run-v
                 ((((empty finished 0) reg-i X) state-reg zero) result-reg X) ; R
                 (((empty input-wire 4) start 1) finishedw 0) ; W
                 (mod                 
                 (always-comb begincase state-reg ;(empty 0 end)
                              ((((empty
                               zero
                                  ((finishedw = 0)
                                  end))
                               four
                                  ((finishedw = 0)
                                  end))
                               two
                                  ((finishedw = 0)
                                  end))
                               three
                                  ((finishedw = 1)
                                  end)
                              )
                              endcase)
                 (always-sync begincase state-reg ;(empty 0 end)
                              ((((empty
                               zero
                                  ((result-reg <= 1) (
                                  (reg-i <= 0) (
                                  (state-reg <= four)
                                  end))))
                               four
                                  ((result-reg <= result-reg) (
                                  (reg-i <= reg-i) (
                                  (state-reg <= ((reg-i < input-wire) ? two : three))
                                  end))))
                               two
                                  ((result-reg <= (result-reg * 2)) (
                                  (state-reg <= four) (
                                  (reg-i <= (reg-i + 1))
                                  end))))
                               three
                                  ((result-reg <= result-reg) (
                                  (state-reg <= three)
                                  ((finished <= finishedw)
                                  end)))
                              )
                              endcase)
                 endmodule)
                 a ) a)


(judgment-holds (run-v
                 ((((empty finished 0) reg-i X) state-reg 0) result-reg X) ; R
                 ((empty input-wire 4) start 1) ; W
                 (mod                  
                  (always-comb begincase state-reg empty endcase)
                  (always-sync begincase state-reg ;(empty 0 end)
                              ((((empty
                               0
                                  ((result-reg <= 1) (
                                  (reg-i <= 0) (
                                  (state-reg <= one)
                                  end))))
                               one
                                  ((result-reg <= result-reg) (
                                  (reg-i <= reg-i) (
                                  (state-reg <= ((reg-i < input-wire) ? 2 : 100))
                                  end))))
                               2
                                  ((result-reg <= (result-reg * 2)) (
                                  (state-reg <= one) (
                                  (reg-i <= (reg-i + 1))
                                  end))))
                               100
                                  ((result-reg <= result-reg) (
                                  (state-reg <= 100)
                                  ((finished <= 1)
                                  end)))
                              )
                              endcase)
                  endmodule)
                 a ) a)


(term "Done all tests")

