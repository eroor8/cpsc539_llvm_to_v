#lang racket
(require
   "llvm_model.rkt"
   racket/match
   redex/reduction-semantics)

; Test metafunctions
(term "Test metafunctions")
(term (different (term 0) (term 1)))
(not (term (different (term 0) (term 0))))
(term (lessereq 0 1))
(term (lessereq 1 1))
(equal? (term (multiply 2 10)) 20)
(not (equal? (term (multiply 2 10)) 1))
(equal? (term (addi 2 10)) 12)
(not (equal? (term (add 2 10)) 10))

(term "Test register lookup, set")
(judgment-holds (reg-lookup ((empty j 10) t 9) j 10)) ; Lookup-Reg-Last
(judgment-holds (reg-lookup ((empty j 10) t 9) t 9)) ; Lookup-Reg-NotLast
(judgment-holds (reg-lookup empty t UNDEFINED)) ; Lookup-Reg-Empty
(judgment-holds (reg-lookup (empty j 10) t UNDEFINED)) ; Lookup-Reg-Not-Found
 
; For some reason, doesn't work with moded judgment... hmmm...
(judgment-holds (reg-set (empty t 9) t 10 R) R)       ; Existing > (empty t 9) 
(judgment-holds (reg-set ((empty t 9) j 10) t 10 R) R) ; Inner > ((empty t 10) j 10)
(judgment-holds (reg-set (empty j 9) t 10 R) R) ; New > ((empty j 9) t 10) 


; Test looking up labels
(term "Test label lookup")
(judgment-holds (label-lookup (label kra (br label fr) (label fr (br label kra) empty)) kra (br label fr))) ; first
(judgment-holds (label-lookup (label kra (br label fr) (label fr (br label kra) empty)) fr (br label kra))) ; second
(judgment-holds (label-lookup empty fr UNDEFINED)) ; empty
(judgment-holds (label-lookup (label kra (br label fr) empty) fr UNDEFINED)) ; second

(term "Test Reduction")
(judgment-holds (-->l (label k (br label k) empty) (empty g 4) ((f = mul nsw i32 g 5) (br label k)) k k ((empty g 4) f 20) (br label k) k k)) ; Step-Mul
(judgment-holds (-->l (label k (br label k) empty) (empty g 4) ((f = add nsw i32 g 5) (br label k)) k k ((empty g 4) f 9) (br label k) k k)) ; Step-Add
(judgment-holds (-->l (label k (br label k) empty) (empty g 4) ((m = phi i32 [g k] [8 n]) (br label k)) k k ((empty g 4) m 4) (br label k) k k)) ; Set-Phi-Reg-First
(judgment-holds (-->l (label k (br label k) empty) (empty g 4) ((m = phi i32 [0 k] [8 n]) (br label k)) k k ((empty g 4) m 0) (br label k) k k)) ; Set-Phi-Value-First
(judgment-holds (-->l (label k (br label k) empty) (empty g 2) ((m = phi i32 [0 k] [g n]) (br label k)) n k ((empty g 2) m 2) (br label k) n k)) ; Set-Phi-Reg-Second
(judgment-holds (-->l (label k (br label k) empty) (empty g 4) ((m = phi i32 [0 k] [8 n]) (br label k)) n k ((empty g 4) m 8) (br label k) n k)) ; Set-Phi-Value-Second
(judgment-holds (-->l (label k (br label k) empty) ((empty g 4) j 9) ((m = icmp sle i32 g j) (br label k)) n k (((empty g 4) j 9) m 1) (br label k) n k)) ; ICMP-Less
(judgment-holds (-->l (label k (br label k) empty) (empty g 4) ((m = icmp sle i32 g g) (br label k)) n k ((empty g 4) m 1) (br label k) n k)) ; ICMP-Not-Less
(judgment-holds (-->l (label kr (br label fr) empty) (empty g 4) (br label kr) kr fr (empty g 4) (br label fr) fr kr)) ; Branch
(judgment-holds (-->l (label kr (br label fr) (label fr (br label kr) empty)) (empty g 1) (br i1 g label kr label fr) kr fr (empty g 1) (br label fr) fr kr)) ; Br-i1
(judgment-holds (-->l (label kr (br label fr) (label fr (br label kr) empty)) (empty g 4) (br i1 g label kr label fr) kr fr (empty g 4) (br label kr) fr fr)) ; Br-i0

(term "Test Conversion")
(judgment-holds (-->l+ (label main ((g = add nsw i32 g 1) (ret i32 g)) empty) (empty g 5) ((g = add nsw i32 g 1) (ret i32 g)) main main (empty g 6) (ret i32 g) main main))
(judgment-holds (-->l+ (label main ((g = add nsw i32 g 1) ((g = mul nsw i32 g 2) (ret i32 g))) empty) (empty g 5) ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) main main (empty g 6) ((g = add nsw i32 g 1) (ret i32 g)) main main))
(judgment-holds (-->l+ (label main ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) empty) (empty g 5) ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) main main (empty g 7) (ret i32 g) main main))
(judgment-holds (-->l+ (label main ((g = add nsw i32 g 1) ((g = mul nsw i32 g 2) (ret i32 g))) empty) (empty g 5) ((g = add nsw i32 g 1) ((g = mul nsw i32 g 2) (ret i32 g))) main main (empty g 12) (ret i32 g) main main))

(term "Test Evaluation")
(judgment-holds (eval (label main ((g = add nsw i32 g 1) (ret i32 g)) empty) (empty g 5) 6))
(judgment-holds (eval (label main ((g = add nsw i32 g 1) ((g = mul nsw i32 g 2) (ret i32 g))) empty) (empty g 5) 12))

;Example: Compute 2^rd
(judgment-holds (eval (label main (br label one) (label one ((rv = phi i32 [1 main] [rfour two]) ((ri = phi i32 [1 main] [rfive two]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three)))) (label two ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label one))) (label three (ret i32 rv) empty)))) (empty rd 5) 32))

(judgment-holds (eval (label main (br label one) (label one ((rv = phi i32 [1 main] [rfour two]) ((ri = phi i32 [1 main] [rfive two]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three)))) (label two ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label one))) (label three (ret i32 rv) empty)))) (empty rd 1) 2))
