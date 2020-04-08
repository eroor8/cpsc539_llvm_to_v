#lang racket
(require
   "llvm_model.rkt"
   "verilog_model.rkt"
   racket/match
   redex/reduction-semantics)
(provide (all-defined-out))


(define-union-language LLVM-Verilog-Union (ll. MyLLVM) (vv. MyVerilog))

(define-judgment-form  LLVM-Verilog-Union
  #:contract (translate-instr ll.l vv.l-nonblocking)
  #:mode (translate-instr     I    O)

  [-----
   (translate-instr (br label ll.lbl-i) ((laststate <= nextstate) (nextstate <= ll.lbl-i)))]
  [-----
   (translate-instr (br i1 ll.reg-i label ll.lbl-i label ll.lbl-i_2)
   ((laststate <= nextstate) (nextstate <= ((ll.reg-i == 1) ? ll.lbl-i : ll.lbl-i_2))))]
  [-----
   (translate-instr (ret i32 ll.reg-i)
      ((finished <= 1) (result-reg <= ll.reg-i)))]


  [(translate-instr ll.l vv.l-nonblocking)
   -----
   (translate-instr ((ll.reg-i = icmp sle i32 ll.reg-i_2 ll.reg-i_3) ll.l) ((ll.reg-i <= (~ (ll.reg-i_2 > ll.reg-i_3))) vv.l-nonblocking))]
   [(translate-instr ll.l vv.l-nonblocking)
   -----
   (translate-instr ((ll.reg-i = mul nsw i32 ll.reg-i_2 ll.a) ll.l) ((ll.reg-i <= (ll.reg-i_2 * ll.a)) vv.l-nonblocking))]
  [(translate-instr ll.l vv.l-nonblocking)
   -----
   (translate-instr ((ll.reg-i = add nsw i32 ll.reg-i_2 ll.a) ll.l) ((ll.reg-i <= (ll.reg-i_2 + ll.a)) vv.l-nonblocking))]

  [(translate-instr ll.l vv.l-nonblocking)
   -----
   (translate-instr ((ll.reg-i = phi i32 [ll.a-or-r ll.lbl-i] [ll.a-or-r_1 ll.lbl-i_1]) ll.l)
                    ((ll.reg-i <= ((laststate == ll.lbl-i) ? ll.a-or-r : ((laststate == ll.lbl-i_1) ? ll.a-or-r_1 : X))) vv.l-nonblocking))]
)

(define-judgment-form  LLVM-Verilog-Union
  #:contract (translate-case ll.p vv.case-list)
  #:mode (translate-case     I    O           )
  [-----
   (translate-case empty empty)
   ]
  [(translate-instr ll.l vv.l-nonblocking)
   (translate-case ll.p vv.case-list_0)
   -----
   (translate-case (label ll.lbl-i ll.l ll.p)
                   (vv.case-list_0 ll.lbl-i vv.l-nonblocking))
  ]
)

(define-judgment-form  LLVM-Verilog-Union
  #:contract (translate-program ll.p vv.p vv.R)
  #:mode (translate-program     I    O    O )
  [(translate-case ll.p vv.case-list)
   -----
   (translate-program ll.p
       (mod
        (always-sync begincase nextstate vv.case-list endcase)
        endmodule
       )
       empty ;((((empty laststate X) curstate 0) result-reg X) finished 0)
   )
  ]
)

