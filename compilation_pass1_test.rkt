#lang racket
(require
   "llvm_model.rkt"
   "compilation_pass1.rkt"
   racket/match
   redex/reduction-semantics)
(provide (all-defined-out))

(term "Test replace-phis")
(judgment-holds (replace-phis ((ret i32 labeltry) (ret i32 labeltest)) (empty lbl-orig lbl-new) ((ret i32 labeltry) (ret i32 labeltest))))
(judgment-holds (replace-phis
                 ((reg-test = phi i32 [3 lbl-test] [2 lbl-test]) (ret i32 labeltest))
                 (empty lbl-orig lbl-new)
                 ((reg-test = phi i32 (3 lbl-test) (3 lbl-test)) (ret i32 labeltest))))
(judgment-holds (replace-phis
                 ((reg-test = phi i32 [3 lbl-orig] [2 lbl-test]) (ret i32 labeltest))
                 (empty lbl-orig lbl-new)
                 ((reg-test = phi i32 (3 lbl-new) (3 lbl-test)) (ret i32 labeltest))))
(judgment-holds (replace-phis (ret i32 labeltest) (empty lbl-orig lbl-new) (ret i32 labeltest)))
(judgment-holds (replace-phis
                 ((ret i32 labeltry) ((reg-test = phi i32 [3 lbl-test] [2 lbl-orig]) (ret i32 labeltest)))
                 (empty lbl-orig lbl-new)
                 ((ret i32 labeltry) ((reg-test = phi i32 (3 lbl-test) (3 lbl-new)) (ret i32 labeltest)))))
(judgment-holds (replace-phis
                 ((rv = phi i32 [1 main] [rfour two]) ((ri = phi i32 [1 main] [rfive two]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three))))
                 ((empty main 17) two 2)
                 ((rv = phi i32 (1 17) (1 2)) ((ri = phi i32 (1 17) (1 2)) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three))))))


(term "Test relabel phis")
(judgment-holds (replace-all-phis (label lbl-test (ret i32 labeltest) empty) (empty lbl-orig lbl-new) (label lbl-test (ret i32 labeltest) empty)))
(judgment-holds (replace-all-phis
                 (label lbl-test ((ret i32 labeltry) ((reg-test = phi i32 [3 lbl-test] [2 lbl-orig]) (ret i32 labeltest))) empty)
                 (empty lbl-orig lbl-new) (label
   lbl-test
   ((ret i32 labeltry)
    ((reg-test = phi i32 (3 lbl-test) (3 lbl-new)) (ret i32 labeltest)))
   empty)))
(judgment-holds (replace-all-phis (label lbl-test ((ret i32 labeltry) ((reg-test = phi i32 [3 lbl-test] [2 lbl-orig]) (ret i32 labeltest)))
                                     (label lbl-orig ((ret i32 kk) ((reg-test = phi i32 [3 lbl-orig] [2 lbl-kk]) (ret i32 lbl-orig)))
                                            empty)) (empty lbl-orig lbl-new)
   (label
   lbl-test
   ((ret i32 labeltry)
    ((reg-test = phi i32 (3 lbl-test) (3 lbl-new)) (ret i32 labeltest)))
   (label
    lbl-orig
    ((ret i32 kk)
     ((reg-test = phi i32 (3 lbl-new) (3 lbl-kk)) (ret i32 lbl-orig)))
    empty))))
(judgment-holds (replace-all-phis
                 (label main (br label one) (label one ((rv = phi i32 [1 main] [rfour two]) ((ri = phi i32 [1 main] [rfive two]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three)))) (label two ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label one))) (label three (ret i32 rv) empty))))
                 ((empty main 17) two 2)
                 (label
   main
   (br label one)
   (label
    one
    ((rv = phi i32 (1 17) (1 2))
     ((ri = phi i32 (1 17) (1 2))
      ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three))))
    (label
     two
     ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1) (br label one)))
     (label three (ret i32 rv) empty))))))


(term "Test relabelling instrs")
(judgment-holds (-->pass1a 0 empty empty empty))
(judgment-holds (-->pass1a 0 (label testlbl (ret i32 rv) empty) (label testlbl (ret i32 rv) empty) empty))
(judgment-holds (-->pass1a 0 (label testlbl ((g = add nsw i32 g 1) (ret i32 g)) empty)
                          (label
   testlbl
   ((g = add nsw i32 g 1) (br label 0))
   (label 0 (ret i32 g) empty))
                           (empty testlbl 0)))
(judgment-holds (-->pass1a 0 (label testlbl ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) empty)
                          (label
   testlbl
   ((g = add nsw i32 g 1) (br label 0))
   (label 0 ((g = add nsw i32 g 1) (br label 1)) (label 1 (ret i32 g) empty)))
                          ((empty 0 1) testlbl 1)))
(judgment-holds (-->pass1a 0 (label main ((g = add nsw i32 g 1) (br label one))
                           (label three ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) empty))
                          (label
   main
   ((g = add nsw i32 g 1) (br label 0))
   (label
    0
    (br label one)
    (label
     three
     ((g = add nsw i32 g 1) (br label 2))
     (label
      2
      ((g = add nsw i32 g 1) (br label 3))
      (label 3 (ret i32 g) empty)))))
                          (((empty 2 3) three 3) main 0)))

(judgment-holds (-->pass1a 0
                          (label main (br label one) (label one ((rv = phi i32 [1 main] [rfour two]) ((ri = phi i32 [1 main] [rfive two]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three)))) (label two ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label one))) (label three (ret i32 rv) empty))))
                          (label
   main
   (br label one)
   (label
    one
    ((rv = phi i32 (1 main) (rfour two)) (br label 1))
    (label
     1
     ((ri = phi i32 (1 main) (rfive two)) (br label 2))
     (label
      2
      ((rtwo = icmp sle i32 ri rd) (br label 3))
      (label
       3
       (br i1 rtwo label two label three)
       (label
        two
        ((rfour = mul nsw i32 rv 2) (br label 5))
        (label
         5
         ((rfive = add nsw i32 ri 1) (br label 6))
         (label 6 (br label one) (label three (ret i32 rv) empty)))))))))
                          (((((empty 5 6) two 6) 2 3) 1 3) one 3)))

(term "Test Pass1")
(judgment-holds (-->pass1 empty empty))
(judgment-holds (-->pass1 (label testlbl (ret i32 rv) empty) (label testlbl (ret i32 rv) empty)))
(judgment-holds (-->pass1 (label testlbl ((g = add nsw i32 g 1) (ret i32 g)) empty)
                          (label
   testlbl
   ((g = add nsw i32 g 1) (br label 0))
   (label 0 (ret i32 g) empty))))
(judgment-holds (-->pass1 (label testlbl ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) empty)
                          (label
   testlbl
   ((g = add nsw i32 g 1) (br label 0))
   (label 0 ((g = add nsw i32 g 1) (br label 1)) (label 1 (ret i32 g) empty)))
                          ))
(judgment-holds (-->pass1 (label main ((g = add nsw i32 g 1) (br label one))
                           (label three ((g = add nsw i32 g 1) ((g = add nsw i32 g 1) (ret i32 g))) empty))
                          (label
   main
   ((g = add nsw i32 g 1) (br label 0))
   (label
    0
    (br label one)
    (label
     three
     ((g = add nsw i32 g 1) (br label 2))
     (label
      2
      ((g = add nsw i32 g 1) (br label 3))
      (label 3 (ret i32 g) empty)))))
                          ))

(judgment-holds (-->pass1
                          (label main (br label one) (label one ((rv = phi i32 [1 main] [rfour two]) ((ri = phi i32 [1 main] [rfive two]) ((rtwo = icmp sle i32 ri rd) (br i1 rtwo label two label three)))) (label two ((rfour = mul nsw i32 rv 2) ((rfive = add nsw i32 ri 1)(br label one))) (label three (ret i32 rv) empty))))
                          (label
   main
   (br label one)
   (label
    one
    ((rv = phi i32 (1 main) (rfour 6)) (br label 1))
    (label
     1
     ((ri = phi i32 (1 main) (rfive 6)) (br label 2))
     (label
      2
      ((rtwo = icmp sle i32 ri rd) (br label 3))
      (label
       3
       (br i1 rtwo label two label three)
       (label
        two
        ((rfour = mul nsw i32 rv 2) (br label 5))
        (label
         5
         ((rfive = add nsw i32 ri 1) (br label 6))
         (label 6 (br label one) (label three (ret i32 rv) empty)))))))))
                          ))

