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
  [a ::= integer X]
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
         (e || e)
         (e && e)
         (e + e)
         (e - e)
         (~ e)
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
  different : any any -> any
  [(different any_1 any_2) ,(not (equal? (term any_1) (term any_2)))])
(define-metafunction MyVerilog    ; define more than
  greater : any any -> any
  [(greater any_1 any_2) ,(> (term any_1) (term any_2))])
(define-metafunction MyVerilog    ; define less than
  lesser : any any -> any
  [(lesser any_1 any_2) ,(< (term any_1) (term any_2))])
(define-metafunction MyVerilog   ; define multiplication
  multiply : any any -> any
  [(multiply any_1 any_2) , (* (term any_1) (term any_2))])
(define-metafunction MyVerilog    ; define addition
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

; Test metafunctions
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

; Lookup reg-i index to find corresponding value
(define-judgment-form MyVerilog
  #:contract (reg-lookup R reg-i a)
  #:mode (reg-lookup I I O)
  ; Matching key is last pair
  [----- "Lookup-Reg-Last"
   (reg-lookup (R reg-i a) reg-i a)]
  ; Matching key is not last pair
  [(reg-lookup R reg-i_2 a_2)
   ----- "Lookup-Reg-NotLast"
   (reg-lookup (R reg-i_1 a_1) reg-i_2 a_2)]
)

(judgment-holds (reg-lookup ((empty j 10) t 9) j 10)) ; Lookup-Reg-Last
(judgment-holds (reg-lookup ((empty j 10) t 9) t 9)) ; Lookup-Reg-NotLast

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
(judgment-holds (wire-lookup ((empty f X) g (reg-1 + 5)) f X))
(judgment-holds (wire-lookup ((empty f 10) g (reg-1 + 5)) g (reg-1 + 5)))
 
; Set register reg-i to value a in new register file
(define-judgment-form  MyVerilog
  #:contract (reg-set R reg-i a R)
  #:mode (reg-set I I I O)
  ; Replace existing key
  [
   ----- "Set-Reg-Existing"
   (reg-set (R reg-i a) reg-i a_2 (R reg-i a_2))]
  [(reg-lookup R reg-i_2 a_4)
   (where #t (different reg-i reg-i_2))
   (reg-set R reg-i_2 a_2 R_2)
   ----- "Set-Reg-Existing-Inner"
   (reg-set (R reg-i a) reg-i_2 a_2 (R_2 reg-i a))]
)
 
(judgment-holds (reg-set (empty t 9) t 10 (empty t 10)))       ; Existing > (empty t 9) 
(judgment-holds (reg-set ((empty t 9) j 10) t 10 ((empty t 10) j 10))) ; Inner > ((empty t 10) j 10)

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
 
(judgment-holds (wire-set (empty wire-1 7) wire-1 (reg-i + 5) (empty wire-1 (reg-i + 5)))) 
(judgment-holds (wire-set ((empty wire-1 7) wire-2 1) wire-1 (reg-1 + (4 + reg-2)) ((empty wire-1 (reg-1 + (4 + reg-2))) wire-2 1))) 
(judgment-holds (wire-set ((empty wire-1 7) wire-2 X) wire-2 (reg-1 + (4 + reg-2)) ((empty wire-1 7) wire-2 (reg-1 + (4 + reg-2))))) 

; Step expression - same as for a functional language!
(define-judgment-form  MyVerilog
  #:contract (--> R W e e)
  #:mode (--> I I I O)
  ;; equality
  [(where #t (same integer_1 integer))
   -----
   (--> R W (integer_1 == integer) 1)]
  [(where #f (same integer_1 integer))
   -----
   (--> R W (integer_1 == integer) 0)]
  [-----
   (--> R W (a == X) X)]
  [-----
   (--> R W (X == a) X)]

  ;; less
  [(where #t (lesser integer_1 integer))
   -----
   (--> R W (integer_1 < integer) 1)]
  [(where #f (lesser integer_1 integer))
   -----
   (--> R W (integer_1 < integer) 0)]
  [-----
   (--> R W (a < X) X)]
  [-----
   (--> R W (X < a) X)]

  ;;  greater
  [(where #t (greater integer_1 integer))
   -----
   (--> R W (integer_1 > integer) 1)]
  [(where #f (greater integer_1 integer))
   -----
   (--> R W (integer_1 > integer) 0)]
  [-----
   (--> R W (X > a) X)]
  [-----
   (--> R W (a_1 > X) X)]

  ;;  multiplication
  [(where a_2 (multiply integer integer_1))
   -----
   (--> R W (integer_1 * integer) a_2)]
  [-----
   (--> R W (a * X) X)]
  [-----
   (--> R W (X * a) X)]

  ;;  addition
  [(where a_2 (addi integer integer_1))
   -----
   (--> R W (integer_1 + integer) a_2)]
  [-----
   (--> R W (X + a) X)]
  [-----
   (--> R W (a + X) X)]

  ;;  subtraction
  [(where a_2 (subi integer_1 integer))
   -----
   (--> R W (integer_1 - integer) a_2)]
  [-----
   (--> R W (X - a) X)]
  [-----
   (--> R W (a - X) X)]

  ;;  not
  [(where #t (different integer 0))
   -----
   (--> R W (~ integer) 0)]
  [-----
   (--> R W (~ 0) 1)]
  [-----
   (--> R W (~ X) X)]
  
  ;;  shift left
  [(where a_2 (shift-left integer_1 integer))
   -----
   (--> R W (integer_1 <<< integer) a_2)]
  [-----
   (--> R W (X <<< a) X)]
  [-----
   (--> R W (a <<< X) X)]
  
  ;;  logical and
  [(where #t (different integer 0))
   (where #t (different integer_1 0))
   -----
   (--> R W (integer_1 && integer) 1)]
  [(where #f (different integer 0))
   -----
   (--> R W (a && integer) 0)]
  [(where #f (different integer 0))
   -----
   (--> R W (integer && a) 0)]
  [(where #t (different integer_1 0))
   -----
   (--> R W (X && integer_1) X)]
  [(where #t (different integer 0))
   -----
   (--> R W (integer && X) X)]
  [-----
   (--> R W (X && X) X)]

  ;;  logical or
  [(where #t (different integer 0))
   -----
   (--> R W (integer || a) 1)]
  [(where #t (different integer 0))
   -----
   (--> R W (a || integer) 1)]
  [(where #f (different integer_1 0))
   (where #f (different integer_1 0))
   -----
   (--> R W (integer_1 || integer) 0)]
  [(where #f (different integer 0))
   -----
   (--> R W (X || integer) X)]
  [(where #f (different integer 0))
   -----
   (--> R W (integer || X) X)]
  [----
   (--> R W (X || X) X)]
  
  ; register and wire references
  [(reg-lookup R reg-i a)
   -----
   (--> R W reg-i a)]
  [(wire-lookup W wire-i e)
   -----
   (--> R W wire-i e)]
)

(judgment-holds (--> empty empty (7 == 7) 1)) 
(judgment-holds (--> empty empty (X == 7) X)) 
(judgment-holds (--> empty empty (7 == X) X)) 
(judgment-holds (--> empty empty (X == X) X)) 
(judgment-holds (--> empty empty (7 == 2) 0)) 
(judgment-holds (--> empty empty (7 < 10) 1)) 
(judgment-holds (--> empty empty (X < 7) X)) 
(judgment-holds (--> empty empty (7 < X) X)) 
(judgment-holds (--> empty empty (X < X) X)) 
(judgment-holds (--> empty empty (7 < 7) 0)) 
(judgment-holds (--> empty empty (7 > 8) 0)) 
(judgment-holds (--> empty empty (X > 7) X)) 
(judgment-holds (--> empty empty (7 > X) X))
(judgment-holds (--> empty empty (X > X) X)) 
(judgment-holds (--> empty empty (7 > 2) 1))
(judgment-holds (--> empty empty (X * 7) X)) 
(judgment-holds (--> empty empty (7 * X) X)) 
(judgment-holds (--> empty empty (X * X) X)) 
(judgment-holds (--> empty empty (7 * 2) 14))
(judgment-holds (--> empty empty (7 * 0) 0))
(judgment-holds (--> empty empty (X + 7) X)) 
(judgment-holds (--> empty empty (7 + X) X)) 
(judgment-holds (--> empty empty (X + X) X)) 
(judgment-holds (--> empty empty (7 + 2) 9))
(judgment-holds (--> empty empty (7 + 0) 7))
(judgment-holds (--> empty empty (X - 7) X)) 
(judgment-holds (--> empty empty (7 - X) X)) 
(judgment-holds (--> empty empty (0 - 2) -2))
(judgment-holds (--> empty empty (7 - 2) 5))
(judgment-holds (--> empty empty (X <<< 7) X)) 
(judgment-holds (--> empty empty (7 <<< X) X)) 
(judgment-holds (--> empty empty (X <<< X) X)) 
(judgment-holds (--> empty empty (8 <<< 2) 32))
(judgment-holds (--> empty empty (7 <<< 0) 7))
(judgment-holds (--> empty empty (~ X) X)) 
(judgment-holds (--> empty empty (~ 0) 1))
(judgment-holds (--> empty empty (~ 7) 0))
(judgment-holds (--> empty empty (X && 7) X)) 
(judgment-holds (--> empty empty (7 && X) X)) 
(judgment-holds (--> empty empty (X && X) X))
(judgment-holds (--> empty empty (0 && X) 0))
(judgment-holds (--> empty empty (X && 0) 0)) 
(judgment-holds (--> empty empty (8 && 2) 1))
(judgment-holds (--> empty empty (1 && 0) 0))
(judgment-holds (--> empty empty (0 && 1) 0))
(judgment-holds (--> empty empty (X || 7) 1))
(judgment-holds (--> empty empty (5 || X) 1))  
(judgment-holds (--> empty empty (X || 0) X)) 
(judgment-holds (--> empty empty (X || X) X)) 
(judgment-holds (--> empty empty (0 || 1) 1))
(judgment-holds (--> empty empty (7 || 0) 1))
(judgment-holds (--> empty empty (7 || 1) 1))
(judgment-holds (--> empty empty (0 || 0) 0))
(judgment-holds (--> (empty f 5) empty f 5)) 
(judgment-holds (--> empty (empty f (reg-i + 3)) f (reg-i + 3))) 

; Conversion relations
(define-judgment-form  MyVerilog ; evaluate expression
  #:contract (eval e a R W)
  #:mode (--> I I I O)
  [(--> R W e e)
   -----
   (-->+ R W e e)]
  [(-->+ R W e_1 e_11)  ; ==
   -----
   (-->+ R W (e == e_1) (e == e_11)]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 == e) (e_11 == e)]
   ; <
   ; >
   ; *
   ; +
   ; <<<
   ; -
   ; ~
   ; &&
   ; ||
  
  ;[(-->+ R W e e_1)
  ; (--> R W e_1 e_2)
  ; -----
  ; (-->+ R W e e_2)]
  
)

(judgment-holds (--> empty (empty f (reg-i + 3)) f (reg-i + 3))) 


(define-judgment-form  MyVerilog ; evaluate expression
  #:contract (eval e a R W)
  [(-->( e a R W)
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


; Next steps
; Finish expression evaluation
; Steps and evaluation for going through sync and comb logic
; 
