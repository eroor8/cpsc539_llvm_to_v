#lang racket
(require
   "verilog_model.rkt"
   "expression_evaluation.rkt"
   racket/match
   redex/reduction-semantics)

(provide -->b -->nb)

 
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
;  ; Do one nonblocking (synchronous) instruction (<=)
  #:contract (-->nb R R W l-nonblocking R l-nonblocking)
  #:mode     (-->nb I I I I          O O         )
;  ; Lookup input register in the register file, multiply by the value, set reg-i
  [(eval-e R W e a)
   (reg-set R_1 reg-i a R_2)
   -----
   (-->nb R R_1 W ((reg-i <= e) l-nonblocking) R_2 l-nonblocking)]
  )


;(define-judgment-form  MyVerilog
  ; Step many times
  ; p c R -> a
  ; Where p is the program, c is the starting label and
  ; R are the input registers
 ; #:contract (run-b p R l c c R l c c)
 ; #:mode     (run-b I I I I I O O O O)
 ; [(-->b R W ((wire-i = e) l-blocking) W_2 l-blocking)
 ;  (run-b p R_10 l_10 c_10 c_11 R_2 l_2 c_2 c_3)
 ;  ----- "Run"
 ;  (run p R l c_0 c_1 R_2 l_2 c_2 c_3)]
 ; [(--> p R l c_0 c_1 R_2 l_2 c_2 c_3)
 ;  ----- "Run-Single"
 ;  (run p R l c_0 c_1 R_2 l_2 c_2 c_3)]
 ; )

;(define-judgment-form  MyVerilog ; evaluate blocking instr
;  #:contract (eval-b l-blocking R W a)
;  [(-->b R W ((wire-i = e) l-blocking) W_2 l-blocking)
;   -----
;   (eval-b end R W W_2)]
;  [(wire-set W wire-i e W_2)
;   -----
;   (eval-b ((wire-i = e) l-blocking) R W_2 0)]
;)

;(define-judgment-form  MyVerilog ; evaluate nonblocking instr
;  #:contract (eval-nb l-nonblocking a R W)
;  [(-->nb R R_1 W ((reg-i <= e) l-nonblocking) R_2 l-nonblocking)
;   -----
;   (eval-nb l-nonblocking a R W)]
;)

