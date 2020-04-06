#lang racket
(require
   "verilog_model.rkt"
   "expression_evaluation.rkt"
   racket/match
   redex/reduction-semantics)

(provide -->b -->nb eval-b eval-nb eval-always-comb eval-always-sync cycle run-v)

;;  Assignments are evaluated more like assembly load/store instructions
;;    - --> steps through a single instruction
;;    - eval-b/nb executes the whole block of instructions and returns a set of regs or wires
;;    - eval-always-sync/comb chooses the right section of the case statement
;;      to execute based on state register and evaluates those assignments
;;    - run: evaluate each always block until finished!
 
(define-judgment-form  MyVerilog
  ; Do one blocking (combinational) instruction (=)
  #:contract (-->b R W l-blocking W l-blocking)
  #:mode     (-->b I I I          O O         )
  ; Lookup input register in the register file, multiply by the value, set reg-i
  [(wire-set W wire-i e W_2)
   -----
   (-->b R W ((wire-i = e) l-blocking) W_2 l-blocking)]
  )

(define-judgment-form  MyVerilog
  ; Do one nonblocking (synchronous) instruction (<=)
  #:contract (-->nb R R W l-nonblocking R l-nonblocking)
  #:mode     (-->nb I I I I          O O         )
  ; Lookup input register in the register file, multiply by the value, set reg-i
  [(eval-e R W e a)
   (reg-set R_1 reg-i a R_2)
   -----
   (-->nb R R_1 W ((reg-i <= e) l-nonblocking) R_2 l-nonblocking)]
  )

(define-judgment-form  MyVerilog
  #:contract (eval-b R W l-blocking W )
  #:mode     (eval-b I I I          O )
  [(-->b R W l-blocking W_2 l-blocking_2)
   (eval-b R W_2 l-blocking_2 W_3)
   ----- 
   (eval-b R W l-blocking W_3)]
  [
   ----- 
   (eval-b R W end W)]
)

(define-judgment-form  MyVerilog
  #:contract (eval-nb R R W l-nonblocking R )
  #:mode     (eval-nb I I I I          O )
  [(-->nb R R_1 W l-nonblocking R_3 l-nonblocking_2)
   (eval-nb R R_3 W l-nonblocking_2 R_2)
   ----- 
   (eval-nb R R_1 W l-nonblocking R_2)]
  [
   ----- 
   (eval-nb R R_1 W end R_1)]
)

(define-judgment-form  MyVerilog
  #:contract (eval-always-comb R W comb-logic-block W)
  #:mode     (eval-always-comb I I I                O )
  [(case-lookup R case-list reg-i l-blocking) 
   (eval-b R W l-blocking W_1)
   ----- 
   (eval-always-comb R W
       (always-comb begincase reg-i case-list endcase)
   W_1)]
)

(define-judgment-form  MyVerilog
  #:contract (eval-always-sync R W sync-logic-block R)
  #:mode     (eval-always-sync I I I                O )
  [(case-lookup R case-list reg-i l-nonblocking) 
   (eval-nb R R W l-nonblocking R_1)
   ----- 
   (eval-always-sync R W
       (always-sync begincase reg-i case-list endcase)
   R_1)]
)


(define-judgment-form  MyVerilog
  #:contract (cycle R W sync-logic-block comb-logic-block R W)
  #:mode     (cycle I I I                I                O O)
  [(eval-always-comb R W comb-logic-block W_1)
   (eval-always-sync R W_1 sync-logic-block R_1)
   ----- 
   (cycle R W sync-logic-block comb-logic-block R_1 W_1)]
)

(define-judgment-form  MyVerilog
  #:contract (run-v R W sync-logic-block comb-logic-block a)
  #:mode     (run-v I I I                I                O)
  [(cycle R (W finished X) sync-logic-block comb-logic-block R_1 W_1)
   (run-v R_1 W_1 sync-logic-block comb-logic-block a)
   ----- 
   (run-v
    R
    (W finished X)
    sync-logic-block comb-logic-block a)]
  [(cycle R (W finished 0) sync-logic-block comb-logic-block R_1 W_1)
   (run-v R_1 W_1 sync-logic-block comb-logic-block a)
   ----- 
   (run-v
    R
    (W finished 0)
    sync-logic-block comb-logic-block a)]
  [----- 
   (run-v
    (R result-reg a)
    (W finished   1)
    sync-logic-block comb-logic-block a)]
)



; evaluation of whole always blocks
; Many clock cycles
