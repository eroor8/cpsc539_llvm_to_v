#lang racket
; Notes:
;   assume that comb blocks dont have loops
;   assume one combinational block, one synchronous block and one list
;      of initializations
;   assume only blocking assignments in comb blocks,
;      only nonblocking assignments in sync. blocks

(require
   racket/match
   redex/reduction-semantics)

(provide (all-defined-out))

(define-language MyVerilog
  ; A program is 'module main beginmodule
  ;                  <initializations>
  ;                  <comb block>
  ;                  <sync block>
  ;               endmodule'
  ; Limitation: only one block of each type
  [P ::= module main beginmodule inits comb-logic sync-logic endmodule]
  [io-type ::= input output none]                ; used in declarations
  [rw-type ::= reg wire]                         ; reg or wire
  [index-decl ::= none [integer : integer]]      ; used to specify bit width
  [a ::= integer]
  [reg-i ::= variable-not-otherwise-mentioned]   ; reg index
  [wire-i ::= variable-not-otherwise-mentioned]  ; reg index
  [rw-i ::= reg-i wire-i]                        ; a register or wire index
  [R ::= empty                                   ; Registers
         (R reg-i integer)]
  [W ::= empty                                   ; Wires
     (W wire-i e)]

  ; Combinational and synchronous logic blocks must contain blocking and
  ; non blocking assignments respectively.
  [comb-logic-block ::= always@(*) begin l-blocking]
  [sync-logic-block ::= always@(posedge clk) begin l-nonblocking]

  ; Expressions : wires, registers, values, computation results
  [e ::= (e == e)
         (e < e)
         (e > e)
         (e > e)
         (e * e)
         (e + e)
         (e <<< e)
         reg-i
         wire-i
         a
  ]
  [case-list-b ::= a l-blocking end]      ; case statement option
  [case-list-nb ::= a l-nonblocking end]

  ; Instructions - includes if else, case, assignments
  [l-blocking ::=
     (if e begin l-blocking else begin l-blocking)
     (case (e) case-list-b endcase)  ; case statement
     (reg-i <= e)                    ; Blocking assignment
     (l-blocking l-blocking)
     end                             ; end of sequence of blocking instrs
     ]
  [l-nonblocking ::=
     (if e begin l-nonblocking else begin l-nonblocking)
     (wire-i = e)                    ; nonblocking assignment
     (l-nonblocking l-nonblocking)
     end
  ]
  ; Initializations specify IOtype, logic type, bit width and name.
  [init ::= (io-type rw-type index-decl rw-i)]
  ; List of initializations.
  ; Should always include clk, result, start, finish
  [inits ::= (inits init)]     ; list of initializations
)

; Define metafunctions to do comparisons, computations
;(define-metafunction MyVerilog
;  shift-left : any any -> any
;  [(shift-left any_1 any_2) ,(* (2 (shift-left any_1 (- any_2 1))))])
(define-metafunction MyVerilog
  same : any any -> any
  [(same any_1 any_2) ,(equal? (term any_1) (term any_2))])
(define-metafunction MyVerilog
    biggest : natural natural -> natural
    [(biggest natural_1 natural_2)
     natural_2
     (side-condition (< (term natural_1) (term natural_2)))]
    [(biggest natural_1 natural_2)
     natural_1])
(define-metafunction MyVerilog
  different : any any -> any
  [(different any_1 any_2) ,(not (equal? (term any_1) (term any_2)))])
(define-metafunction MyVerilog
  greater : any any -> any
  [(greater any_1 any_2) ,(> (term any_1) (term any_2))])
(define-metafunction MyVerilog
  multiply : any any -> any
  [(multiply any_1 any_2) , (* (term any_1) (term any_2))])
(define-metafunction MyVerilog
  add : any any -> any
  [(add any_1 any_2) , (+ (term any_1) (term any_2))])

(define-judgment-form MyVerilog
  #:contract (reg-lookup R reg-i a)
  #:mode (reg-lookup I I O)
  [-----
   (reg-lookup (R reg-i a) reg-i a)]
  [(reg-lookup R reg-i_2 a_2)
   -----
   (reg-lookup (R reg-i_1 a_1) reg-i_2 a_2)])

(define-judgment-form MyVerilog
  #:contract (wire-lookup W wire-i e)
  #:mode (wire-lookup I I O)
  [-----
   (wire-lookup (W wire-i e) wire-i e)]
  [(wire-lookup W wire-i_2 e_2)
   -----
   (wire-lookup (W wire-i_1 e_1) wire-i_2 e_2)])

(define-judgment-form  MyVerilog
  #:contract (reg-set R reg-i a R)
  #:mode (reg-set I I I O)
  [-----
   (reg-set (R reg-i a) reg-i a_2 (R reg-i a_2))]
  [-----
   (reg-set R reg-i a (R reg-i a))])

(define-judgment-form  MyVerilog
  #:contract (wire-set W wire-i e W)
  #:mode (wire-set I I I O)
  [-----
   (wire-set (W wire-i e) wire-i e_2 (W wire-i e_2))]
  [-----
   (wire-set W wire-i e (W wire-i e))])

(define-judgment-form  MyVerilog ; step expression
  #:contract (--> e e R W)
  [(where #t (same a_1 a))
   -----
   (--> (a_1 == a) 1 R W)]
  [(reg-lookup R reg-i a)
   -----
   (--> reg-i a R W)]
  [(reg-lookup W wire-i e)
   -----
   (--> wire-i e R W)]
)

(define-judgment-form  MyVerilog ; evaluate expression
  #:contract (eval e a R W)
  [(--> e a R W)
   -----
   (eval e a R W)]
)

;(define-judgment-form  MyVerilog ; evaluate blocking instr
;  #:contract (eval-b l-blocking R W a)
;  [
;   -----
;   (eval-b end R W 1)]
;  [(wire-set W wire-i e W_2)
;   -----
;   (eval-b ((wire-i = e) l-blocking) R W_2 0)]
;)

;(define-judgment-form  MyVerilog ; evaluate nonblocking instr
;  #:contract (eval-nb l-nonblocking a R W)
;  [(--> e l-nonblocking a R W)
;   -----
;   (eval-nb l-nonblocking a R W)]
;)
