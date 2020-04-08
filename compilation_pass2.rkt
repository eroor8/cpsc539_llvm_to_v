#lang racket
(require
   "llvm_model.rkt"
   "verilog_model.rkt"
   racket/match
   redex/reduction-semantics)
(provide (all-defined-out))


(define-union-language LLVM-Verilog-Union (ll. MyLLVM) (vv. MyVerilog))

(define-judgment-form  LLVM-Verilog-Union
  #:contract (translate-instr ll.R ll.l vv.l-nonblocking vv.R)
  #:mode (translate-instr     I I    O                O) 

  [-----
   (translate-instr ll.R (br label ll.lbl-i) ((laststate <= nextstate) ((nextstate <= ll.lbl-i) end)) ll.R)]
  [-----
   (translate-instr ll.R (br i1 ll.reg-i label ll.lbl-i label ll.lbl-i_2)
   ((laststate <= nextstate) ((nextstate <= ((ll.reg-i == 1) ? ll.lbl-i : ll.lbl-i_2)) end)) ll.R)]
  [-----
   (translate-instr ll.R (ret i32 ll.reg-i)
      ((finished <= 1) ((result-reg <= ll.reg-i) end)) ll.R )]


  [(translate-instr ll.R ll.l vv.l-nonblocking vv.R_2)
   -----
   (translate-instr ll.R ((ll.reg-i = icmp sle i32 ll.reg-i_2 ll.reg-i_3) ll.l) ((ll.reg-i <= (~ (ll.reg-i_2 > ll.reg-i_3))) vv.l-nonblocking) (vv.R_2 ll.reg-i X))]
   [(translate-instr ll.R ll.l vv.l-nonblocking vv.R_2)
   -----
   (translate-instr ll.R ((ll.reg-i = mul nsw i32 ll.reg-i_2 ll.a) ll.l) ((ll.reg-i <= (ll.reg-i_2 * ll.a)) vv.l-nonblocking) (vv.R_2 ll.reg-i X))]
  [(translate-instr ll.R ll.l vv.l-nonblocking vv.R_2)
   -----
   (translate-instr ll.R ((ll.reg-i = add nsw i32 ll.reg-i_2 ll.a) ll.l) ((ll.reg-i <= (ll.reg-i_2 + ll.a)) vv.l-nonblocking) (vv.R_2 ll.reg-i X))]

  [(translate-instr ll.R ll.l vv.l-nonblocking vv.R_2)
   -----
   (translate-instr ll.R ((ll.reg-i = phi i32 [ll.a-or-r ll.lbl-i] [ll.a-or-r_1 ll.lbl-i_1]) ll.l)
                    ((ll.reg-i <= ((laststate == ll.lbl-i) ? ll.a-or-r : ((laststate == ll.lbl-i_1) ? ll.a-or-r_1 : X))) vv.l-nonblocking) (vv.R_2 ll.reg-i X))]
)

(define-judgment-form  LLVM-Verilog-Union
  #:contract (translate-case ll.R ll.p vv.case-list vv.R)
  #:mode (translate-case     I I    O            O)
  [-----
   (translate-case ll.R empty empty ll.R)
   ]
  [(translate-instr ll.R ll.l vv.l-nonblocking ll.R_2)
   (translate-case ll.R_2 ll.p vv.case-list_0 vv.R_3)
   -----
   (translate-case ll.R (label ll.lbl-i ll.l ll.p)
                   (vv.case-list_0 ll.lbl-i vv.l-nonblocking) vv.R_3)
  ]
)

(define-judgment-form  LLVM-Verilog-Union
  #:contract (-->pass2 ll.p ll.R vv.p vv.R)
  #:mode (-->pass2     I    I    O    O )
  [(translate-case ll.R ll.p vv.case-list vv.R)
   -----
   (-->pass2 ll.p ll.R
       (mod
        (always-comb begincase nextstate empty endcase)
        (always-sync begincase nextstate vv.case-list endcase)
        endmodule
       )
       ((((vv.R laststate X) nextstate entry) result-reg X) finished 0)
   )
  ]
)

