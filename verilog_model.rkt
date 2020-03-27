#lang racket
; assume that comb blocks dont have loops

(require
   racket/match
   redex/reduction-semantics)

(provide (all-defined-out))

(define-language MyVerilog
  [P ::= module any beginmodule inits comb-logic sync-logic endmodule]
  [io-type ::= input output none]
  [rw-type ::= reg wire]
  [index-decl ::= none [integer : integer]]           ; value types
  [a-or-r ::= a reg-i]
  [a ::= integer]
  [reg-i ::= variable-not-otherwise-mentioned]   ; reg index
  [wire-i ::= variable-not-otherwise-mentioned]  ; reg index
  [e ::= reg-i wire-i a c]  ; reg index
  [rw-i ::= reg-i wire-i]  ; reg index
  [R ::= finish                                   ; Registers
         (R reg-i integer)]                      
  [W ::= empty                                    ; Wires
         (W wire-i e)]                   
  [comb-logic ::= empty                              
         (comb-logic comb-logic-block)]      
  [sync-logic ::= empty                           
         (sync-logic sync-logic-block)]    
  [comb-logic-block ::= always@(*) begin l-blocking]
  [sync-logic-block ::= always@(posedge clk) begin l-nonblocking]
  [c ::= (e == e)                        ; conditions   
         (e < e)                             ; branch to label e
         (e > e)                             ; branch to label e
         (e > e) 
         (e * e)                      ; conditions   
         (e + e)                      ; branch to label e
         (e <<< e)                    ; branch to label e
  ]
  [case-list-b ::= a l-blocking end]
  [case-list-nb ::= a l-nonblocking end]
  [l-blocking ::=                                ; instructions   
     (if e begin l-blocking else begin l-blocking)
     (case (e) case-list-b endcase)
     (reg-i <= e)
     (l-blocking l-blocking)
     end
  ]
  [l-nonblocking ::=                             ; instructions   
     (if e begin l-nonblocking else begin l-nonblocking)
     (wire-i = e)
     (l-nonblocking l-nonblocking)
     end
  ]
  [inits ::= empty (inits init)]
  [init ::= (input wire clk) (io-type rw-type index-decl rw-i)]
)

(define-metafunction MyVerilog
  shift-left : any any -> any
  [(shift-left any_1 any_2) ,(* (^ 2 (term any_2)) (term any_1))])

(define-metafunction MyVerilog
  same : any any -> any
  [(same any_1 any_2) ,(equal? (term any_1) (term any_2))])

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

(define-judgment-form  MyVerilog ; evaluate blocking instr
  #:contract (eval-b e a R W a)
  [
   -----
   (eval-b end R W 1)]
  [(wire-set W wire-i e W_2)
   -----
   (eval-b ((wire-i = e) l-blocking) R W_2 0)]
)

(define-judgment-form  MyVerilog ; evaluate nonblocking instr
  #:contract (eval-nb e a R W)
  [(--> e a R W)
   -----
   (eval e a R W)]
)