#lang racket
; Notes:
;   assume that comb blocks dont have loops
;   assume one combinational block, one synchronous block and one list
;      of initializations
;   assume only blocking assignments in comb blocks,
;      only nonblocking assignments in sync. blocks
(require
   "llvm_model.rkt"
   racket/match
   redex/reduction-semantics)

(provide (all-defined-out))

(define-language MyVerilog
  ; A program is 'module main beginmodule
  ;                  <comb block>
  ;                  <sync block>
  ;               endmodule'
  ; Limitation: only one block of each type
  [a ::= integer X]
  [a-or-case ::= a case-i]
  [reg-i ::= variable-not-otherwise-mentioned]   ; reg index
  [wire-i ::= variable-not-otherwise-mentioned]  ; reg index
  [case-i ::= a variable-not-otherwise-mentioned]  ; reg index
  [rw-i ::= reg-i wire-i]                        ; a register or wire index
  [R ::= empty                                   ; Registers
         (R reg-i any)]
  [W ::= empty                                   ; Wires
     (W wire-i e)]
  ; Expressions : wires, registers, values, computation results
  [e ::= (e == e)
         (e < e)
         (e > e)
         (e > e)p
         (e * e)
         (e || e)
         (e && e)
         (e + e)
         (e - e)
         (~ e)
         (e <<< e)
         (e ? e : e)
         reg-i
         wire-i
         case-i
         a
         ]
  [p ::= (mod comb-logic-block sync-logic-block endmodule)
         (mod sync-logic-block endmodule)
  ]
  [l ::= l-blocking l-nonblocking]
  [case-list ::= empty (case-list case-i l)]      ; case statement option

  ; Combinational and synchronous logic blocks must contain blocking and
  ; non blocking assignments respectively.
  ; They need to be structured as case statements. 
  [comb-logic-block ::= (always-comb begincase reg-i case-list endcase)]
  [sync-logic-block ::= (always-sync begincase reg-i case-list endcase)]

  [l-blocking ::=
     ;(if e begin l-blocking else begin l-blocking)
     ;(case (e) case-list-b endcase)  ; case statement
     (wire-i = e)                    ; Blocking assignment
     (l-blocking l-blocking)
     end                             ; end of sequence of blocking instrs
     ]
  [l-nonblocking ::=
     ;(if e begin l-nonblocking else begin l-nonblocking)
     ;(case (e) case-list-nb endcase)  ; case statement
     (reg-i <= e)                     ; nonblocking assignment
     (l-nonblocking l-nonblocking)
     end
  ]
  )


(define-metafunction MyVerilog
  same : any any -> any
  [(same any_1 any_2) ,(equal? (term any_1) (term any_2))])
(define-metafunction MyVerilog    ; define more than
  greater : any any -> any
  [(greater any_1 any_2) ,(> (term any_1) (term any_2))])
(define-metafunction MyVerilog    ; define less than
  lesser : any any -> any
  [(lesser any_1 any_2) ,(< (term any_1) (term any_2))])
(define-metafunction MyLLVM    ; define multiplication
  multiply : any any -> any
  [(multiply any_1 any_2) , (* (term any_1) (term any_2))])
(define-metafunction MyLLVM    ; define addiltion
  addi : any any -> any
  [(addi any_1 any_2) , (+ (term any_1) (term any_2))])
(define-metafunction MyVerilog    ; define subtraction
  subi : any any -> any
  [(subi any any_1) , (+ (term any) (- (term any_1)))])
(define-metafunction MyVerilog    ; define shift left (* 2^any_2)
    shift-left : any any -> any
    [(shift-left any_1 any_2)
     any_1
     (side-condition (< (term any_2) (term 1)))]
    [(shift-left any_1 any_2)
     (multiply 2 (shift-left any_1 (addi any_2 -1)))])
(define-metafunction MyLLVM
  different : any any -> any
  [(different any_1 any_2) ,(not (equal? (term any_1) (term any_2)))])



; Lookup reg-i index to find corresponding value
(define-judgment-form MyVerilog
  #:contract (reg-lookup R reg-i any)
  #:mode (reg-lookup I I O)
  ; Matching key is last pair
  [----- "Lookup-Reg-Last"
   (reg-lookup (R reg-i any_0) reg-i any_0)]
  ; Matching key is not last pair
  [(reg-lookup R reg-i_2 any_2)
   ----- "Lookup-Reg-NotLast"
   (reg-lookup (R reg-i_1 any_1) reg-i_2 any_2)]
)

; Lookup reg-i index to find corresponding value
(define-judgment-form MyVerilog
  #:contract (wire-lookup W wire-i e)
  #:mode (wire-lookup I I O)
  ; Matching key is last pair
  [----- "Lookup-Wire-Last"
   (wire-lookup (W wire-i e) wire-i e)]
  ; Matching key is not last pair
  [(wire-lookup W wire-i_2 e_2)
   ----- "Lookup-Wire-NotLast"
   (wire-lookup (W wire-i_1 e_1) wire-i_2 e_2)]
  )

; Lookup reg-i index to find corresponding value
(define-judgment-form MyVerilog
  #:contract (case-lookup R case-list reg-i l)
  #:mode     (case-lookup I I         I     O)
  ; Matching key is last pair
  [(reg-lookup R reg-i any_0)
   -----
   (case-lookup R (case-list any_0 l) reg-i l)]
  ; Matching key is not last pair
  [(case-lookup R case-list reg-i l_2)
   -----
   (case-lookup R (case-list any_0 l) reg-i l_2)]
)


; Set register reg-i to value a in new register file
(define-judgment-form  MyVerilog
  #:contract (reg-set R reg-i any R)
  #:mode (reg-set I I I O)
  ; Replace existing key
  [
   ----- "Set-Reg-Existing"
   (reg-set (R reg-i any) reg-i any_2 (R reg-i any_2))]
  [(reg-lookup R reg-i_2 any_4)
   (where #t (different reg-i reg-i_2))
   (reg-set R reg-i_2 any_2 R_2)
   ----- "Set-Reg-Existing-Inner"
   (reg-set (R reg-i any) reg-i_2 any_2 (R_2 reg-i any))]
)


; Note: wires are set to expressions, not values.
; This is more true to the actual hardware, since wires correspond to the
; outputs of combinational logic, which evaluates to different results
; depending on the input values. 
(define-judgment-form  MyVerilog
  #:contract (wire-set W wire-i e W)
  #:mode (wire-set I I I O)
  ; Replace existing key
  [
   ----- "Set-Wire-Existing"
   (wire-set (W wire-i e) wire-i e_2 (W wire-i e_2))]
  [(wire-lookup W wire-i_2 e_4)
   (where #t (different wire-i wire-i_2))
   (wire-set W wire-i_2 e_2 W_2)
   ----- "Set-Wire-Existing-Inner"
   (wire-set (W wire-i e) wire-i_2 e_2 (W_2 wire-i e))]
)

