#lang racket
(require
   "verilog_model.rkt"
   racket/match
   redex/reduction-semantics)

(provide -->e -->+ -->* eval-e)

;;  Expressions are evaluated as describted in class:
;;    - Reduction (-->)
;;    - Conversion (-->+)
;;    - Inductive Conversion (-->*)
;;    - Evaluation (eval)

; Reduction of expression - same as for a functional language!
(define-judgment-form  MyVerilog
  #:contract (-->e R W e e)
  #:mode (-->e I I I O)
  ;; equality
  [(where #t (same integer_1 integer))
   -----
   (-->e R W (integer_1 == integer) 1)]
  [(where #f (same integer_1 integer))
   -----
   (-->e R W (integer_1 == integer) 0)]
  [-----
   (-->e R W (a == X) X)]
  [-----
   (-->e R W (X == a) X)]

  ;; less
  [(where #t (lesser integer_1 integer))
   -----
   (-->e R W (integer_1 < integer) 1)]
  [(where #f (lesser integer_1 integer))
   -----
   (-->e R W (integer_1 < integer) 0)]
  [-----
   (-->e R W (a < X) X)]
  [-----
   (-->e R W (X < a) X)]

  ;;  greater
  [(where #t (greater integer_1 integer))
   -----
   (-->e R W (integer_1 > integer) 1)]
  [(where #f (greater integer_1 integer))
   -----
   (-->e R W (integer_1 > integer) 0)]
  [-----
   (-->e R W (X > a) X)]
  [-----
   (-->e R W (a_1 > X) X)]

  ;;  multiplication
  [(where a_2 (multiply integer integer_1))
   -----
   (-->e R W (integer_1 * integer) a_2)]
  [-----
   (-->e R W (a * X) X)]
  [-----
   (-->e R W (X * a) X)]

  ;;  addition
  [(where a_2 (addi integer integer_1))
   -----
   (-->e R W (integer_1 + integer) a_2)]
  [-----
   (-->e R W (X + a) X)]
  [-----
   (-->e R W (a + X) X)]

  ;;  subtraction
  [(where a_2 (subi integer_1 integer))
   -----
   (-->e R W (integer_1 - integer) a_2)]
  [-----
   (-->e R W (X - a) X)]
  [-----
   (-->e R W (a - X) X)]

  ;;  not
  [(where #t (different integer 0))
   -----
   (-->e R W (~ integer) 0)]
  [-----
   (-->e R W (~ 0) 1)]
  [-----
   (-->e R W (~ X) X)]
  
  ;;  shift left
  [(where a_2 (shift-left integer_1 integer))
   -----
   (-->e R W (integer_1 <<< integer) a_2)]
  [-----
   (-->e R W (X <<< a) X)]
  [-----
   (-->e R W (a <<< X) X)]
  
  ;;  logical and
  [(where #t (different integer 0))
   (where #t (different integer_1 0))
   -----
   (-->e R W (integer_1 && integer) 1)]
  [(where #f (different integer 0))
   -----
   (-->e R W (a && integer) 0)]
  [(where #f (different integer 0))
   -----
   (-->e R W (integer && a) 0)]
  [(where #t (different integer_1 0))
   -----
   (-->e R W (X && integer_1) X)]
  [(where #t (different integer 0))
   -----
   (-->e R W (integer && X) X)]
  [-----
   (-->e R W (X && X) X)]

  ;;  logical or
  [(where #t (different integer 0))
   -----
   (-->e R W (integer || a) 1)]
  [(where #t (different integer 0))
   -----
   (-->e R W (a || integer) 1)]
  [(where #f (different integer_1 0))
   (where #f (different integer_1 0))
   -----
   (-->e R W (integer_1 || integer) 0)]
  [(where #f (different integer 0))
   -----
   (-->e R W (X || integer) X)]
  [(where #f (different integer 0))
   -----
   (-->e R W (integer || X) X)]
  [----
   (-->e R W (X || X) X)]
  
  ; (e ? e else e)
  [(where #t (different integer 0))
   -----
   (-->e R W (integer ? e : e_1) e)]
  [(where #f (different integer 0))
   -----
   (-->e R W (integer ? e : e_1) e_1)]
  [-----
   (-->e R W (X ? e : e_1) X)]
  
  ; register and wire references
  [(reg-lookup R reg-i a)
   -----
   (-->e R W reg-i a)]
  [(wire-lookup W wire-i e)
   -----
   (-->e R W wire-i e)]
)

; Conversion relations
(define-judgment-form  MyVerilog ; evaluate expression
  #:contract (-->+ R W e e)
  #:mode (-->+ I I I O)
  [(-->e R W e e_1)
   ----- "Step"
   (-->+ R W e e_1)]
  ; ==
  [(-->+ R W e_1 e_11)  
   ----- "Cont-Eq-2"
   (-->+ R W (e == e_1) (e == e_11))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 == e) (e_11 == e))]
   ; <
  [(-->+ R W e_1 e_11)  
   -----
   (-->+ R W (e < e_1) (e < e_11))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 < e) (e_11 < e))]
   ; >
  [(-->+ R W e_1 e_11)  
   -----
   (-->+ R W (e > e_1) (e > e_11))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 > e) (e_11 > e))]
   ; *
  [(-->+ R W e_1 e_11)  
   -----
   (-->+ R W (e * e_1) (e * e_11))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 * e) (e_11 * e))]
   ; +
  [(-->+ R W e_1 e_11)  
   -----
   (-->+ R W (e + e_1) (e + e_11))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 + e) (e_11 + e))]
   ; -
  [(-->+ R W e_1 e_11)  
   -----
   (-->+ R W (e - e_1) (e - e_11))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 - e) (e_11 - e))]
   ; <<<
  [(-->+ R W e_1 e_11)  
   -----
   (-->+ R W (e <<< e_1) (e <<< e_11))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 <<< e) (e_11 <<< e))]
   ; ~
  [(-->+ R W e_1 e_11)  
   -----
   (-->+ R W (~ e_1) (~ e_11))]
   ; &&
  [(-->+ R W e_1 e_11)  
   -----
   (-->+ R W (e && e_1) (e && e_11))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 && e) (e_11 && e))]
   ; ||
  [(-->+ R W e_1 e_11)  
   -----
   (-->+ R W (e || e_1) (e || e_11))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e_1 || e) (e_11 || e))]
   ; ?
  [(-->+ R W e e_11)  
   -----
   (-->+ R W (e ? e_1 : e_2) (e_11 ? e_1 : e_2))]
  [(-->+ R W e_1 e_11)
   -----
   (-->+ R W (e ? e_1 : e_2) (e ? e_11 : e_2))]
  [(-->+ R W e_2 e_11)
   -----
   (-->+ R W (e ? e_1 : e_2) (e ? e_11 : e_11))]  
  ;[(-->+ R W e e_1)
  ; (--> R W e_1 e_2)
  ; -----
  ; (-->+ R W e e_2))]
  
)

; Conversion
(define-judgment-form  MyVerilog ; evaluate expression
  #:contract (-->* R W e e)
  #:mode (-->* I I I O)
  [
   -----
   (-->*  R W e e)]
  [(-->+  R W e_1 e_2)
   (-->*  R W e_2 e_3)
   -----
   (-->*  R W e_1 e_3)]
)

; Evaluation of an expression
(define-judgment-form  MyVerilog ; evaluate expression
  #:contract (eval-e R W e a)
  #:mode (eval-e I I I O)
  [(-->* R W e a)
   -----
   (eval-e R W e a)]
)
