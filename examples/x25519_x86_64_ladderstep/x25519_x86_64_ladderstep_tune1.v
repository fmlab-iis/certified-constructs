From Coq Require Import ZArith .
From mathcomp Require Import ssreflect ssrbool ssrnat seq .
From Common Require Import Bits .
From mQhasm Require Import bvDSL bvVerify Options .
Set Implicit Arguments .
Unset Strict Implicit .
Import Prenex Implicits .
Open Scope N_scope.
Open Scope bvdsl_scope.

Definition radix51 := @limbs 51 .

Definition check_inputs : VS.t :=
  let '(x10, x11, x12, x13, x14) :=
      (1000, 1001, 1002, 1003, 1004) in
  let '(x20, x21, x22, x23, x24) :=
      (2000, 2001, 2002, 2003, 2004) in
  let '(z20, z21, z22, z23, z24) :=
      (3000, 3001, 3002, 3003, 3004) in
  let '(x30, x31, x32, x33, x34) :=
      (4000, 4001, 4002, 4003, 4004) in
  let '(z30, z31, z32, z33, z34) :=
      (5000, 5001, 5002, 5003, 5004) in
  let '(x1'0, x1'1, x1'2, x1'3, x1'4) :=
      (10000, 10001, 10002, 10003, 10004) in
  let '(x2'0, x2'1, x2'2, x2'3, x2'4) :=
      (20000, 20001, 20002, 20003, 20004) in
  let '(z2'0, z2'1, z2'2, z2'3, z2'4) :=
      (30000, 30001, 30002, 30003, 30004) in
  let '(x3'0, x3'1, x3'2, x3'3, x3'4) :=
      (40000, 40001, 40002, 40003, 40004) in
  let '(z3'0, z3'1, z3'2, z3'3, z3'4) :=
      (50000, 50001, 50002, 50003, 50004) in
  VSLemmas.OP.P.of_list [::
      x10; x11; x12; x13; x14;
      x20; x21; x22; x23; x24;
      z20; z21; z22; z23; z24;
      x30; x31; x32; x33; x34;
      z30; z31; z32; z33; z34
  ] .

Definition check_pre : bexp :=
  let '(x10, x11, x12, x13, x14) :=
      (1000, 1001, 1002, 1003, 1004) in
  let '(x20, x21, x22, x23, x24) :=
      (2000, 2001, 2002, 2003, 2004) in
  let '(z20, z21, z22, z23, z24) :=
      (3000, 3001, 3002, 3003, 3004) in
  let '(x30, x31, x32, x33, x34) :=
      (4000, 4001, 4002, 4003, 4004) in
  let '(z30, z31, z32, z33, z34) :=
      (5000, 5001, 5002, 5003, 5004) in
  let '(x1'0, x1'1, x1'2, x1'3, x1'4) :=
      (10000, 10001, 10002, 10003, 10004) in
  let '(x2'0, x2'1, x2'2, x2'3, x2'4) :=
      (20000, 20001, 20002, 20003, 20004) in
  let '(z2'0, z2'1, z2'2, z2'3, z2'4) :=
      (30000, 30001, 30002, 30003, 30004) in
  let '(x3'0, x3'1, x3'2, x3'3, x3'4) :=
      (40000, 40001, 40002, 40003, 40004) in
  let '(z3'0, z3'1, z3'2, z3'3, z3'4) :=
      (50000, 50001, 50002, 50003, 50004) in
  let max := bvposz ((2^51+2^15)%Z) in
  bvrands [::
             (bvrvar x10) <=r max; (bvrvar x11) <=r max;
             (bvrvar x12) <=r max; (bvrvar x13) <=r max;
             (bvrvar x14) <=r max;
             (bvrvar x20) <=r max; (bvrvar x21) <=r max;
             (bvrvar x22) <=r max; (bvrvar x23) <=r max;
             (bvrvar x24) <=r max;
             (bvrvar z20) <=r max; (bvrvar z21) <=r max;
             (bvrvar z22) <=r max; (bvrvar z23) <=r max;
             (bvrvar z24) <=r max;
             (bvrvar x30) <=r max; (bvrvar x31) <=r max;
             (bvrvar x32) <=r max; (bvrvar x33) <=r max;
             (bvrvar x34) <=r max;
             (bvrvar z30) <=r max; (bvrvar z31) <=r max;
             (bvrvar z32) <=r max; (bvrvar z33) <=r max;
             (bvrvar z34) <=r max
          ].

Definition x25519_x86_64_ladderstep_post1 :=
  let '(x10, x11, x12, x13, x14) :=
      (1000, 1001, 1002, 1003, 1004) in
  let '(x20, x21, x22, x23, x24) :=
      (2000, 2001, 2002, 2003, 2004) in
  let '(z20, z21, z22, z23, z24) :=
      (3000, 3001, 3002, 3003, 3004) in
  let '(x30, x31, x32, x33, x34) :=
      (4000, 4001, 4002, 4003, 4004) in
  let '(z30, z31, z32, z33, z34) :=
      (5000, 5001, 5002, 5003, 5004) in
  let '(x1'0, x1'1, x1'2, x1'3, x1'4) :=
      (10000, 10001, 10002, 10003, 10004) in
  let '(x2'0, x2'1, x2'2, x2'3, x2'4) :=
      (20000, 20001, 20002, 20003, 20004) in
  let '(z2'0, z2'1, z2'2, z2'3, z2'4) :=
      (30000, 30001, 30002, 30003, 30004) in
  let '(x3'0, x3'1, x3'2, x3'3, x3'4) :=
      (40000, 40001, 40002, 40003, 40004) in
  let '(z3'0, z3'1, z3'2, z3'3, z3'4) :=
      (50000, 50001, 50002, 50003, 50004) in
  let X2 := radix51 [:: bvevar x20; bvevar x21; bvevar x22; bvevar x23;
                        bvevar x24 ] in
  let Z2 := radix51 [:: bvevar z20; bvevar z21; bvevar z22; bvevar z23;
                        bvevar z24 ] in
  let X2' := radix51 [:: bvevar x2'0; bvevar x2'1; bvevar x2'2; bvevar x2'3;
                         bvevar x2'4 ] in
  let p25519 := (2^255-19)%Z in
  let max  := bvposz ((2^51+2^15)%Z) in
  bvands2
    [::
       bveEqMod
       X2'
       (bvesq (bvesub (bvesq X2) (bvesq Z2)))
       (bvconst p25519)
    ]
    [::
       (bvrvar x2'0) <=r max; (bvrvar x2'1) <=r max;
       (bvrvar x2'2) <=r max; (bvrvar x2'3) <=r max;
       (bvrvar x2'4) <=r max
    ] .

Definition x25519_x86_64_ladderstep_post2 :=
  let '(x10, x11, x12, x13, x14) :=
      (1000, 1001, 1002, 1003, 1004) in
  let '(x20, x21, x22, x23, x24) :=
      (2000, 2001, 2002, 2003, 2004) in
  let '(z20, z21, z22, z23, z24) :=
      (3000, 3001, 3002, 3003, 3004) in
  let '(x30, x31, x32, x33, x34) :=
      (4000, 4001, 4002, 4003, 4004) in
  let '(z30, z31, z32, z33, z34) :=
      (5000, 5001, 5002, 5003, 5004) in
  let '(x1'0, x1'1, x1'2, x1'3, x1'4) :=
      (10000, 10001, 10002, 10003, 10004) in
  let '(x2'0, x2'1, x2'2, x2'3, x2'4) :=
      (20000, 20001, 20002, 20003, 20004) in
  let '(z2'0, z2'1, z2'2, z2'3, z2'4) :=
      (30000, 30001, 30002, 30003, 30004) in
  let '(x3'0, x3'1, x3'2, x3'3, x3'4) :=
      (40000, 40001, 40002, 40003, 40004) in
  let '(z3'0, z3'1, z3'2, z3'3, z3'4) :=
      (50000, 50001, 50002, 50003, 50004) in
  let X2 := radix51 [:: bvevar x20; bvevar x21; bvevar x22; bvevar x23;
                        bvevar x24] in
  let Z2 := radix51 [:: bvevar z20; bvevar z21; bvevar z22; bvevar z23;
                        bvevar z24] in
  let Z2' := radix51 [:: bvevar z2'0; bvevar z2'1; bvevar z2'2; bvevar z2'3;
                         bvevar z2'4] in
  let p25519 := (2^255-19)%Z in
  let max  := bvposz ((2^51+2^15)%Z) in
  bvands2
    [::
       bveEqMod
       Z2'
       (bvemuls
          [:: bvconst 4%Z; X2; Z2;
              bveadds [:: bvesq X2;
                          bvemuls [:: bvconst 486662%Z; X2; Z2];
                          bvesq Z2]
          ])
       (bvconst p25519)
  ]
  [::
     (bvrvar z2'0) <=r max; (bvrvar z2'1) <=r max;
     (bvrvar z2'2) <=r max; (bvrvar z2'3) <=r max;
     (bvrvar z2'4) <=r max
  ] .

Definition x25519_x86_64_ladderstep_post3 :=
  let '(x10, x11, x12, x13, x14) :=
      (1000, 1001, 1002, 1003, 1004) in
  let '(x20, x21, x22, x23, x24) :=
      (2000, 2001, 2002, 2003, 2004) in
  let '(z20, z21, z22, z23, z24) :=
      (3000, 3001, 3002, 3003, 3004) in
  let '(x30, x31, x32, x33, x34) :=
      (4000, 4001, 4002, 4003, 4004) in
  let '(z30, z31, z32, z33, z34) :=
      (5000, 5001, 5002, 5003, 5004) in
  let '(x1'0, x1'1, x1'2, x1'3, x1'4) :=
      (10000, 10001, 10002, 10003, 10004) in
  let '(x2'0, x2'1, x2'2, x2'3, x2'4) :=
      (20000, 20001, 20002, 20003, 20004) in
  let '(z2'0, z2'1, z2'2, z2'3, z2'4) :=
      (30000, 30001, 30002, 30003, 30004) in
  let '(x3'0, x3'1, x3'2, x3'3, x3'4) :=
      (40000, 40001, 40002, 40003, 40004) in
  let '(z3'0, z3'1, z3'2, z3'3, z3'4) :=
      (50000, 50001, 50002, 50003, 50004) in
  let X1 := radix51 [:: bvevar x10; bvevar x11; bvevar x12; bvevar x13;
                        bvevar x14 ] in
  let X2 := radix51 [:: bvevar x20; bvevar x21; bvevar x22; bvevar x23;
                        bvevar x24 ] in
  let Z2 := radix51 [:: bvevar z20; bvevar z21; bvevar z22; bvevar z23;
                        bvevar z24 ] in
  let X3 := radix51 [:: bvevar x30; bvevar x31; bvevar x32; bvevar x33;
                        bvevar x34 ] in
  let Z3 := radix51 [:: bvevar z30; bvevar z31; bvevar z32; bvevar z33;
                        bvevar z34 ] in
  let X3' := radix51 [:: bvevar x3'0; bvevar x3'1; bvevar x3'2; bvevar x3'3;
                         bvevar x3'4 ] in
  let Z3' := radix51 [:: bvevar z3'0; bvevar z3'1; bvevar z3'2; bvevar z3'3;
                         bvevar z3'4 ] in
  let p25519 := (2^255-19)%Z in
  let max  := bvposz ((2^51+2^15)%Z) in
  bvands2
    [::
       bveEqMod
       (bvemul X3'
             (bvemul X1
                     (bvesq (bvesub (bvemul X3 Z2) (bvemul X2 Z3)))))
       (bvemul Z3'
               (bvesq (bvesub (bvemul X2 X3) (bvemul Z2 Z3))))
       (bvconst p25519)
    ]
    [::
       (bvrvar x3'0) <=r max; (bvrvar x3'1) <=r max;
       (bvrvar x3'2) <=r max; (bvrvar x3'3) <=r max;
       (bvrvar x3'4) <=r max;
       (bvrvar z3'0) <=r max; (bvrvar z3'1) <=r max;
       (bvrvar z3'2) <=r max; (bvrvar z3'3) <=r max;
       (bvrvar z3'4) <=r max
    ] .

Definition x25519_x86_64_ladderstep_post3_1 :=
  let '(x10, x11, x12, x13, x14) :=
      (1000, 1001, 1002, 1003, 1004) in
  let '(x20, x21, x22, x23, x24) :=
      (2000, 2001, 2002, 2003, 2004) in
  let '(z20, z21, z22, z23, z24) :=
      (3000, 3001, 3002, 3003, 3004) in
  let '(x30, x31, x32, x33, x34) :=
      (4000, 4001, 4002, 4003, 4004) in
  let '(z30, z31, z32, z33, z34) :=
      (5000, 5001, 5002, 5003, 5004) in
  let '(x1'0, x1'1, x1'2, x1'3, x1'4) :=
      (10000, 10001, 10002, 10003, 10004) in
  let '(x2'0, x2'1, x2'2, x2'3, x2'4) :=
      (20000, 20001, 20002, 20003, 20004) in
  let '(z2'0, z2'1, z2'2, z2'3, z2'4) :=
      (30000, 30001, 30002, 30003, 30004) in
  let '(x3'0, x3'1, x3'2, x3'3, x3'4) :=
      (40000, 40001, 40002, 40003, 40004) in
  let '(z3'0, z3'1, z3'2, z3'3, z3'4) :=
      (50000, 50001, 50002, 50003, 50004) in
  let X1 := radix51 [:: bvevar x10; bvevar x11; bvevar x12; bvevar x13;
                        bvevar x14 ] in
  let X2 := radix51 [:: bvevar x20; bvevar x21; bvevar x22; bvevar x23;
                        bvevar x24 ] in
  let Z2 := radix51 [:: bvevar z20; bvevar z21; bvevar z22; bvevar z23;
                        bvevar z24 ] in
  let X3 := radix51 [:: bvevar x30; bvevar x31; bvevar x32; bvevar x33;
                        bvevar x34 ] in
  let Z3 := radix51 [:: bvevar z30; bvevar z31; bvevar z32; bvevar z33;
                        bvevar z34 ] in
  let X3' := radix51 [:: bvevar x3'0; bvevar x3'1; bvevar x3'2; bvevar x3'3;
                         bvevar x3'4 ] in
  let Z3' := radix51 [:: bvevar z3'0; bvevar z3'1; bvevar z3'2; bvevar z3'3;
                         bvevar z3'4 ] in
  let p25519 := (2^255-19)%Z in
  let max  := bvposz ((2^51+2^15)%Z) in
  bvands2
    [::
       bveEqMod
       X3'
       (bvemul (bvconst 4%Z)
               (bvesq (bvesub (bvemul X2 X3) (bvemul Z2 Z3))))
       (bvconst p25519)
  ]
  [::
     (bvrvar x3'0) <=r max; (bvrvar x3'1) <=r max;
     (bvrvar x3'2) <=r max; (bvrvar x3'3) <=r max;
     (bvrvar x3'4) <=r max
  ].

Definition x25519_x86_64_ladderstep_post3_2 :=
  let '(x10, x11, x12, x13, x14) :=
      (1000, 1001, 1002, 1003, 1004) in
  let '(x20, x21, x22, x23, x24) :=
      (2000, 2001, 2002, 2003, 2004) in
  let '(z20, z21, z22, z23, z24) :=
      (3000, 3001, 3002, 3003, 3004) in
  let '(x30, x31, x32, x33, x34) :=
      (4000, 4001, 4002, 4003, 4004) in
  let '(z30, z31, z32, z33, z34) :=
      (5000, 5001, 5002, 5003, 5004) in
  let '(x1'0, x1'1, x1'2, x1'3, x1'4) :=
      (10000, 10001, 10002, 10003, 10004) in
  let '(x2'0, x2'1, x2'2, x2'3, x2'4) :=
      (20000, 20001, 20002, 20003, 20004) in
  let '(z2'0, z2'1, z2'2, z2'3, z2'4) :=
      (30000, 30001, 30002, 30003, 30004) in
  let '(x3'0, x3'1, x3'2, x3'3, x3'4) :=
      (40000, 40001, 40002, 40003, 40004) in
  let '(z3'0, z3'1, z3'2, z3'3, z3'4) :=
      (50000, 50001, 50002, 50003, 50004) in
  let X1 := radix51 [:: bvevar x10; bvevar x11; bvevar x12; bvevar x13;
                        bvevar x14 ] in
  let X2 := radix51 [:: bvevar x20; bvevar x21; bvevar x22; bvevar x23;
                        bvevar x24 ] in
  let Z2 := radix51 [:: bvevar z20; bvevar z21; bvevar z22; bvevar z23;
                        bvevar z24 ] in
  let X3 := radix51 [:: bvevar x30; bvevar x31; bvevar x32; bvevar x33;
                        bvevar x34 ] in
  let Z3 := radix51 [:: bvevar z30; bvevar z31; bvevar z32; bvevar z33;
                        bvevar z34 ] in
  let X3' := radix51 [:: bvevar x3'0; bvevar x3'1; bvevar x3'2; bvevar x3'3;
                         bvevar x3'4 ] in
  let Z3' := radix51 [:: bvevar z3'0; bvevar z3'1; bvevar z3'2; bvevar z3'3;
                         bvevar z3'4 ] in
  let p25519 := (2^255-19)%Z in
  let max  := bvposz ((2^51+2^15)%Z) in
  bvands2
    [::
       bveEqMod
       Z3'
       (bvemul (bvconst 4%Z)
               (bvemul X1
                       (bvesq (bvesub (bvemul X3 Z2)
                                      (bvemul X2 Z3)))))
       (bvconst p25519)
    ]
    [::
       (bvrvar z3'0) <=r max; (bvrvar z3'1) <=r max;
       (bvrvar z3'2) <=r max; (bvrvar z3'3) <=r max;
       (bvrvar z3'4) <=r max
    ] .

Definition x25519_x86_64_ladderstep_post : bexp :=
  bvands [:: x25519_x86_64_ladderstep_post1;
             x25519_x86_64_ladderstep_post2;
             x25519_x86_64_ladderstep_post3 ].

Definition program :=

let L0x7fffffffd930 := 7 in 
let L0x7fffffffd938 := 14 in
let L0x7fffffffd940 := 54 in
let L0x7fffffffd948 := 49 in
let L0x7fffffffd950 := 13 in

let L0x7fffffffd958 := 30 in
let L0x7fffffffd960 := 57 in
let L0x7fffffffd968 := 52 in
let L0x7fffffffd970 := 17 in
let L0x7fffffffd978 := 11 in

let L0x7fffffffd980 := 27 in
let L0x7fffffffd988 := 39 in
let L0x7fffffffd990 := 73 in
let L0x7fffffffd998 := 75 in
let L0x7fffffffd9a0 := 15 in

let L0x7fffffffd9a8 := 9 in
let L0x7fffffffd9b0 := 61 in
let L0x7fffffffd9b8 := 67 in
let L0x7fffffffd9c0 := 21 in
let L0x7fffffffd9c8 := 26 in

let L0x7fffffffd9d0 := 65 in
let L0x7fffffffd9d8 := 59 in
let L0x7fffffffd9e0 := 25 in
let L0x7fffffffd9e8 := 12 in
let L0x7fffffffd9f0 := 71 in

let L0x7fffffffd9f8 := 31 in
let L0x7fffffffda00 := 77 in
let L0x7fffffffda08 := 72 in
let L0x7fffffffda10 := 50 in
let L0x7fffffffda18 := 55 in
let L0x7fffffffda20 := 5 in
let L0x7fffffffda28 := 10 in
let L0x7fffffffda30 := 53 in
let L0x7fffffffda38 := 48 in
let L0x7fffffffda40 := 22 in

let L0x7fffffffda48 := 8 in

let L0x7fffffffda50 := 56 in

let L0x7fffffffda90 := 66 in     (* work[0] *)
let L0x7fffffffda98 := 47 in
let L0x7fffffffdaa0 := 60 in
let L0x7fffffffdaa8 := 76 in
let L0x7fffffffdab0 := 28 in

let L0x7fffffffdab8 := 23 in     (* work[1] *)
let L0x7fffffffdac0 := 64 in
let L0x7fffffffdac8 := 58 in
let L0x7fffffffdad0 := 33 in
let L0x7fffffffdad8 := 38 in

let L0x7fffffffdae0 := 70 in     (* work[2] *)
let L0x7fffffffdae8 := 62 in
let L0x7fffffffdaf0 := 36 in
let L0x7fffffffdaf8 := 40 in
let L0x7fffffffdb00 := 19 in

let L0x7fffffffdb08 := 2 in      (* work[3] *)
let L0x7fffffffdb10 := 3 in
let L0x7fffffffdb18 := 74 in
let L0x7fffffffdb20 := 34 in
let L0x7fffffffdb28 := 29 in

let L0x7fffffffdb30 := 63 in     (* work[4] *)
let L0x7fffffffdb38 := 16 in
let L0x7fffffffdb40 := 1 in
let L0x7fffffffdb48 := 18 in
let L0x7fffffffdb50 := 51 in

let L0x603150 := 37 in           (* 0x0007FFFFFFFFFFFF = 2251799813685247 *)

let L0x603158 := 32 in           (* 996687872 *)

let L0x603160 := 0 in            (* 0x000FFFFFFFFFFFDA = 4503599627370458 *)
let L0x603168 := 4 in            (* 0x000FFFFFFFFFFFFE = 4503599627370494 *)

let r9 := 6 in
let r13 := 20 in
let rcx := 24 in
let rax := 35 in
let r14 := 41 in
let r15 := 42 in
let r12 := 43 in
let rsi := 44 in
let r10 := 45 in
let r11 := 46 in
let r8 := 68 in
let rdx := 69 in

let carry := 999 in
let tmp   := 998 in
let tmp0  := 997 in
let tmp1  := 996 in

let '(x10, x11, x12, x13, x14) :=
    (1000, 1001, 1002, 1003, 1004) in
let '(x20, x21, x22, x23, x24) :=
    (2000, 2001, 2002, 2003, 2004) in
let '(z20, z21, z22, z23, z24) :=
    (3000, 3001, 3002, 3003, 3004) in
let '(x30, x31, x32, x33, x34) :=
    (4000, 4001, 4002, 4003, 4004) in
let '(z30, z31, z32, z33, z34) :=
    (5000, 5001, 5002, 5003, 5004) in
let '(x1'0, x1'1, x1'2, x1'3, x1'4) :=
    (10000, 10001, 10002, 10003, 10004) in
let '(x2'0, x2'1, x2'2, x2'3, x2'4) :=
    (20000, 20001, 20002, 20003, 20004) in
let '(z2'0, z2'1, z2'2, z2'3, z2'4) :=
    (30000, 30001, 30002, 30003, 30004) in
let '(x3'0, x3'1, x3'2, x3'3, x3'4) :=
    (40000, 40001, 40002, 40003, 40004) in
let '(z3'0, z3'1, z3'2, z3'3, z3'4) :=
    (50000, 50001, 50002, 50003, 50004) in

[::

bvAssign L0x7fffffffda90 (bvVar x10);
bvAssign L0x7fffffffda98 (bvVar x11);
bvAssign L0x7fffffffdaa0 (bvVar x12);
bvAssign L0x7fffffffdaa8 (bvVar x13);
bvAssign L0x7fffffffdab0 (bvVar x14);

bvAssign L0x7fffffffdab8 (bvVar x20);
bvAssign L0x7fffffffdac0 (bvVar x21);
bvAssign L0x7fffffffdac8 (bvVar x22);
bvAssign L0x7fffffffdad0 (bvVar x23);
bvAssign L0x7fffffffdad8 (bvVar x24);

bvAssign L0x7fffffffdae0 (bvVar z20);
bvAssign L0x7fffffffdae8 (bvVar z21);
bvAssign L0x7fffffffdaf0 (bvVar z22);
bvAssign L0x7fffffffdaf8 (bvVar z23);
bvAssign L0x7fffffffdb00 (bvVar z24);

bvAssign L0x7fffffffdb08 (bvVar x30);
bvAssign L0x7fffffffdb10 (bvVar x31);
bvAssign L0x7fffffffdb18 (bvVar x32);
bvAssign L0x7fffffffdb20 (bvVar x33);
bvAssign L0x7fffffffdb28 (bvVar x34);

bvAssign L0x7fffffffdb30 (bvVar z30);
bvAssign L0x7fffffffdb38 (bvVar z31);
bvAssign L0x7fffffffdb40 (bvVar z32);
bvAssign L0x7fffffffdb48 (bvVar z33);
bvAssign L0x7fffffffdb50 (bvVar z34);

bvAssign L0x603150 (bvConst (fromPosZ 2251799813685247%Z));

bvAssign L0x603158 (bvConst (fromPosZ 996687872%Z));

bvAssign L0x603160 (bvConst (fromPosZ 4503599627370458%Z));
bvAssign L0x603168 (bvConst (fromPosZ 4503599627370494%Z));

(* mov    0x28(%rdi),%rsi                          #! EA = L0x7fffffffdab8 *)
bvAssign rsi (bvVar L0x7fffffffdab8);
(* mov    0x30(%rdi),%rdx                          #! EA = L0x7fffffffdac0 *)
bvAssign rdx (bvVar L0x7fffffffdac0);
(* mov    0x38(%rdi),%rcx                          #! EA = L0x7fffffffdac8 *)
bvAssign rcx (bvVar L0x7fffffffdac8);
(* mov    0x40(%rdi),%r8                           #! EA = L0x7fffffffdad0 *)
bvAssign r8 (bvVar L0x7fffffffdad0);
(* mov    0x48(%rdi),%r9                           #! EA = L0x7fffffffdad8 *)
bvAssign r9 (bvVar L0x7fffffffdad8);
(* mov    %rsi,%rax *)
bvAssign rax (bvVar rsi);
(* mov    %rdx,%r10 *)
bvAssign r10 (bvVar rdx);
(* mov    %rcx,%r11 *)
bvAssign r11 (bvVar rcx);
(* mov    %r8,%r12 *)
bvAssign r12 (bvVar r8);
(* mov    %r9,%r13 *)
bvAssign r13 (bvVar r9);
(* add    0x20245f(%rip),%rax        # 0x603160    #! EA = L0x603160 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rax (bvVar L0x603160) (bvVar rax);
(* add    0x202460(%rip),%r10        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar L0x603168) (bvVar r10);
(* add    0x202459(%rip),%r11        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r11 (bvVar L0x603168) (bvVar r11);
(* add    0x202452(%rip),%r12        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar L0x603168) (bvVar r12);
(* add    0x20244b(%rip),%r13        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r13 (bvVar L0x603168) (bvVar r13);
(* add    0x50(%rdi),%rsi                          #! EA = L0x7fffffffdae0 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar L0x7fffffffdae0) (bvVar rsi);
(* add    0x58(%rdi),%rdx                          #! EA = L0x7fffffffdae8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rdx (bvVar L0x7fffffffdae8) (bvVar rdx);
(* add    0x60(%rdi),%rcx                          #! EA = L0x7fffffffdaf0 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar L0x7fffffffdaf0) (bvVar rcx);
(* add    0x68(%rdi),%r8                           #! EA = L0x7fffffffdaf8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar L0x7fffffffdaf8) (bvVar r8);
(* add    0x70(%rdi),%r9                           #! EA = L0x7fffffffdb00 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r9 (bvVar L0x7fffffffdb00) (bvVar r9);
(* sub    0x50(%rdi),%rax                          #! EA = L0x7fffffffdae0 *)
bvSub rax (bvVar rax) (bvVar L0x7fffffffdae0);
(* sub    0x58(%rdi),%r10                          #! EA = L0x7fffffffdae8 *)
bvSub r10 (bvVar r10) (bvVar L0x7fffffffdae8);
(* sub    0x60(%rdi),%r11                          #! EA = L0x7fffffffdaf0 *)
bvSub r11 (bvVar r11) (bvVar L0x7fffffffdaf0);
(* sub    0x68(%rdi),%r12                          #! EA = L0x7fffffffdaf8 *)
bvSub r12 (bvVar r12) (bvVar L0x7fffffffdaf8);
(* sub    0x70(%rdi),%r13                          #! EA = L0x7fffffffdb00 *)
bvSub r13 (bvVar r13) (bvVar L0x7fffffffdb00);
(* mov    %rsi,(%rsp)                              #! EA = L0x7fffffffd930 *)
bvAssign L0x7fffffffd930 (bvVar rsi);
(* mov    %rdx,0x8(%rsp)                           #! EA = L0x7fffffffd938 *)
bvAssign L0x7fffffffd938 (bvVar rdx);
(* mov    %rcx,0x10(%rsp)                          #! EA = L0x7fffffffd940 *)
bvAssign L0x7fffffffd940 (bvVar rcx);
(* mov    %r8,0x18(%rsp)                           #! EA = L0x7fffffffd948 *)
bvAssign L0x7fffffffd948 (bvVar r8);
(* mov    %r9,0x20(%rsp)                           #! EA = L0x7fffffffd950 *)
bvAssign L0x7fffffffd950 (bvVar r9);
(* mov    %rax,0x28(%rsp)                          #! EA = L0x7fffffffd958 *)
bvAssign L0x7fffffffd958 (bvVar rax);
(* mov    %r10,0x30(%rsp)                          #! EA = L0x7fffffffd960 *)
bvAssign L0x7fffffffd960 (bvVar r10);
(* mov    %r11,0x38(%rsp)                          #! EA = L0x7fffffffd968 *)
bvAssign L0x7fffffffd968 (bvVar r11);
(* mov    %r12,0x40(%rsp)                          #! EA = L0x7fffffffd970 *)
bvAssign L0x7fffffffd970 (bvVar r12);
(* mov    %r13,0x48(%rsp)                          #! EA = L0x7fffffffd978 *)
bvAssign L0x7fffffffd978 (bvVar r13);
(* mov    0x28(%rsp),%rax                          #! EA = L0x7fffffffd958 *)
bvAssign rax (bvVar L0x7fffffffd958);
(* mulq   0x28(%rsp)                               #! EA = L0x7fffffffd958 *)
bvMulf rdx rax (bvVar L0x7fffffffd958) (bvVar rax);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    0x28(%rsp),%rax                          #! EA = L0x7fffffffd958 *)
bvAssign rax (bvVar L0x7fffffffd958);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x30(%rsp)                               #! EA = L0x7fffffffd960 *)
bvMulf rdx rax (bvVar L0x7fffffffd960) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0x28(%rsp),%rax                          #! EA = L0x7fffffffd958 *)
bvAssign rax (bvVar L0x7fffffffd958);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x38(%rsp)                               #! EA = L0x7fffffffd968 *)
bvMulf rdx rax (bvVar L0x7fffffffd968) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    0x28(%rsp),%rax                          #! EA = L0x7fffffffd958 *)
bvAssign rax (bvVar L0x7fffffffd958);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x40(%rsp)                               #! EA = L0x7fffffffd970 *)
bvMulf rdx rax (bvVar L0x7fffffffd970) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    0x28(%rsp),%rax                          #! EA = L0x7fffffffd958 *)
bvAssign rax (bvVar L0x7fffffffd958);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    0x30(%rsp),%rax                          #! EA = L0x7fffffffd960 *)
bvAssign rax (bvVar L0x7fffffffd960);
(* mulq   0x30(%rsp)                               #! EA = L0x7fffffffd960 *)
bvMulf rdx rax (bvVar L0x7fffffffd960) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x30(%rsp),%rax                          #! EA = L0x7fffffffd960 *)
bvAssign rax (bvVar L0x7fffffffd960);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x38(%rsp)                               #! EA = L0x7fffffffd968 *)
bvMulf rdx rax (bvVar L0x7fffffffd968) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x30(%rsp),%rax                          #! EA = L0x7fffffffd960 *)
bvAssign rax (bvVar L0x7fffffffd960);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x40(%rsp)                               #! EA = L0x7fffffffd970 *)
bvMulf rdx rax (bvVar L0x7fffffffd970) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x30(%rsp),%rdx                          #! EA = L0x7fffffffd960 *)
bvAssign rdx (bvVar L0x7fffffffd960);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x38(%rsp),%rax                          #! EA = L0x7fffffffd968 *)
bvAssign rax (bvVar L0x7fffffffd968);
(* mulq   0x38(%rsp)                               #! EA = L0x7fffffffd968 *)
bvMulf rdx rax (bvVar L0x7fffffffd968) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x38(%rsp),%rdx                          #! EA = L0x7fffffffd968 *)
bvAssign rdx (bvVar L0x7fffffffd968);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x40(%rsp)                               #! EA = L0x7fffffffd970 *)
bvMulf rdx rax (bvVar L0x7fffffffd970) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x38(%rsp),%rdx                          #! EA = L0x7fffffffd968 *)
bvAssign rdx (bvVar L0x7fffffffd968);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x40(%rsp),%rdx                          #! EA = L0x7fffffffd970 *)
bvAssign rdx (bvVar L0x7fffffffd970);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x40(%rsp)                               #! EA = L0x7fffffffd970 *)
bvMulf rdx rax (bvVar L0x7fffffffd970) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x40(%rsp),%rdx                          #! EA = L0x7fffffffd970 *)
bvAssign rdx (bvVar L0x7fffffffd970);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x48(%rsp),%rdx                          #! EA = L0x7fffffffd978 *)
bvAssign rdx (bvVar L0x7fffffffd978);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x2022b9(%rip),%rdx        # 0x603150    #! EA = L0x603150 *)
bvAssign rdx (bvVar L0x603150);
(* shld   $0xd,%rsi,%rcx *)
(* NOTE: merge 'shld $0xd,%rsi,%rcx' with 'and %rdx,%rsi *)
bvConcatShl rcx rsi (bvVar rcx) (bvVar rsi) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
(* shld   $0xd,%r8,%r9 *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rdx,%r8 *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
(* add    %rcx,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rcx) (bvVar r8);
(* shld   $0xd,%r10,%r11 *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rdx,%r10 *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
(* add    %r9,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
(* shld   $0xd,%r12,%r13 *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rdx,%r12 *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* and    %rdx,%r12 *)
(* NOTE: merged, see above *)
(* add    %r11,%r12 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
(* shld   $0xd,%r14,%r15 *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rdx,%r14 *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* and    %rdx,%r14 *)
(* NOTE: merged, see above *)
(* add    %r13,%r14 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
(* imul   $0x13,%r15,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar r15);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* mov    %rsi,%rcx *)
bvAssign rcx (bvVar rsi);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r8,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r8) (bvVar rcx);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
bvAssign rsi (bvVar tmp);
(* mov    %rcx,%r8 *)
bvAssign r8 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r8' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r10,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r10) (bvVar rcx);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
bvAssign r8 (bvVar tmp);
(* mov    %rcx,%r9 *)
bvAssign r9 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r9' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r12,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r12) (bvVar rcx);
(* and    %rdx,%r9 *)
(* NOTE: merged, see above *)
bvAssign r9 (bvVar tmp);
(* mov    %rcx,%rax *)
bvAssign rax (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rax' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r14,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r14) (bvVar rcx);
(* and    %rdx,%rax *)
(* NOTE: merged, see above *)
bvAssign rax (bvVar tmp);
(* mov    %rcx,%r10 *)
bvAssign r10 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r10' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* imul   $0x13,%rcx,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar rcx);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
bvAssign r10 (bvVar tmp);
(* mov    %rsi,0x50(%rsp)                          #! EA = L0x7fffffffd980 *)
bvAssign L0x7fffffffd980 (bvVar rsi);
(* mov    %r8,0x58(%rsp)                           #! EA = L0x7fffffffd988 *)
bvAssign L0x7fffffffd988 (bvVar r8);
(* mov    %r9,0x60(%rsp)                           #! EA = L0x7fffffffd990 *)
bvAssign L0x7fffffffd990 (bvVar r9);
(* mov    %rax,0x68(%rsp)                          #! EA = L0x7fffffffd998 *)
bvAssign L0x7fffffffd998 (bvVar rax);
(* mov    %r10,0x70(%rsp)                          #! EA = L0x7fffffffd9a0 *)
bvAssign L0x7fffffffd9a0 (bvVar r10);
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* mulq   (%rsp)                                   #! EA = L0x7fffffffd930 *)
bvMulf rdx rax (bvVar L0x7fffffffd930) (bvVar rax);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x8(%rsp)                                #! EA = L0x7fffffffd938 *)
bvMulf rdx rax (bvVar L0x7fffffffd938) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x10(%rsp)                               #! EA = L0x7fffffffd940 *)
bvMulf rdx rax (bvVar L0x7fffffffd940) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x18(%rsp)                               #! EA = L0x7fffffffd948 *)
bvMulf rdx rax (bvVar L0x7fffffffd948) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0x8(%rsp)                                #! EA = L0x7fffffffd938 *)
bvMulf rdx rax (bvVar L0x7fffffffd938) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x10(%rsp)                               #! EA = L0x7fffffffd940 *)
bvMulf rdx rax (bvVar L0x7fffffffd940) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x18(%rsp)                               #! EA = L0x7fffffffd948 *)
bvMulf rdx rax (bvVar L0x7fffffffd948) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x8(%rsp),%rdx                           #! EA = L0x7fffffffd938 *)
bvAssign rdx (bvVar L0x7fffffffd938);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x10(%rsp),%rax                          #! EA = L0x7fffffffd940 *)
bvAssign rax (bvVar L0x7fffffffd940);
(* mulq   0x10(%rsp)                               #! EA = L0x7fffffffd940 *)
bvMulf rdx rax (bvVar L0x7fffffffd940) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x10(%rsp),%rdx                          #! EA = L0x7fffffffd940 *)
bvAssign rdx (bvVar L0x7fffffffd940);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x18(%rsp)                               #! EA = L0x7fffffffd948 *)
bvMulf rdx rax (bvVar L0x7fffffffd948) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x10(%rsp),%rdx                          #! EA = L0x7fffffffd940 *)
bvAssign rdx (bvVar L0x7fffffffd940);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x18(%rsp),%rdx                          #! EA = L0x7fffffffd948 *)
bvAssign rdx (bvVar L0x7fffffffd948);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x18(%rsp)                               #! EA = L0x7fffffffd948 *)
bvMulf rdx rax (bvVar L0x7fffffffd948) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x18(%rsp),%rdx                          #! EA = L0x7fffffffd948 *)
bvAssign rdx (bvVar L0x7fffffffd948);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x20(%rsp),%rdx                          #! EA = L0x7fffffffd950 *)
bvAssign rdx (bvVar L0x7fffffffd950);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x202105(%rip),%rdx        # 0x603150    #! EA = L0x603150 *)
bvAssign rdx (bvVar L0x603150);
(* shld   $0xd,%rsi,%rcx *)
(* NOTE: merge 'shld $0xd,%rsi,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx rsi (bvVar rcx) (bvVar rsi) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
(* shld   $0xd,%r8,%r9 *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rdx,%r8' *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
(* add    %rcx,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rcx) (bvVar r8);
(* shld   $0xd,%r10,%r11 *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rdx,%r10' *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
(* add    %r9,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
(* shld   $0xd,%r12,%r13 *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rdx,%r12' *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* and    %rdx,%r12 *)
(* NOTE: merged, see above *)
(* add    %r11,%r12 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
(* shld   $0xd,%r14,%r15 *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rdx,%r14' *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* and    %rdx,%r14 *)
(* NOTE: merged, see above *)
(* add    %r13,%r14 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
(* imul   $0x13,%r15,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar r15);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* mov    %rsi,%rcx *)
bvAssign rcx (bvVar rsi);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r8,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r8) (bvVar rcx);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
bvAssign rsi (bvVar tmp);
(* mov    %rcx,%r8 *)
bvAssign r8 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r8' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r10,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r10) (bvVar rcx);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
bvAssign r8 (bvVar tmp);
(* mov    %rcx,%r9 *)
bvAssign r9 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r9' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r12,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r12) (bvVar rcx);
(* and    %rdx,%r9 *)
(* NOTE: merged, see above *)
bvAssign r9 (bvVar tmp);
(* mov    %rcx,%rax *)
bvAssign rax (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rax' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r14,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r14) (bvVar rcx);
(* and    %rdx,%rax *)
(* NOTE: merged, see above *)
bvAssign rax (bvVar tmp);
(* mov    %rcx,%r10 *)
bvAssign r10 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r10' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* imul   $0x13,%rcx,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar rcx);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
bvAssign r10 (bvVar tmp);
(* mov    %rsi,0x78(%rsp)                          #! EA = L0x7fffffffd9a8 *)
bvAssign L0x7fffffffd9a8 (bvVar rsi);
(* mov    %r8,0x80(%rsp)                           #! EA = L0x7fffffffd9b0 *)
bvAssign L0x7fffffffd9b0 (bvVar r8);
(* mov    %r9,0x88(%rsp)                           #! EA = L0x7fffffffd9b8 *)
bvAssign L0x7fffffffd9b8 (bvVar r9);
(* mov    %rax,0x90(%rsp)                          #! EA = L0x7fffffffd9c0 *)
bvAssign L0x7fffffffd9c0 (bvVar rax);
(* mov    %r10,0x98(%rsp)                          #! EA = L0x7fffffffd9c8 *)
bvAssign L0x7fffffffd9c8 (bvVar r10);
(* mov    %rsi,%rsi *)
bvAssign rsi (bvVar rsi);
(* mov    %r8,%rdx *)
bvAssign rdx (bvVar r8);
(* mov    %r9,%rcx *)
bvAssign rcx (bvVar r9);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %r10,%r9 *)
bvAssign r9 (bvVar r10);
(* add    0x20205a(%rip),%rsi        # 0x603160    #! EA = L0x603160 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar L0x603160) (bvVar rsi);
(* add    0x20205b(%rip),%rdx        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rdx (bvVar L0x603168) (bvVar rdx);
(* add    0x202054(%rip),%rcx        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar L0x603168) (bvVar rcx);
(* add    0x20204d(%rip),%r8        # 0x603168     #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar L0x603168) (bvVar r8);
(* add    0x202046(%rip),%r9        # 0x603168     #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r9 (bvVar L0x603168) (bvVar r9);
(* sub    0x50(%rsp),%rsi                          #! EA = L0x7fffffffd980 *)
bvSub rsi (bvVar rsi) (bvVar L0x7fffffffd980);
(* sub    0x58(%rsp),%rdx                          #! EA = L0x7fffffffd988 *)
bvSub rdx (bvVar rdx) (bvVar L0x7fffffffd988);
(* sub    0x60(%rsp),%rcx                          #! EA = L0x7fffffffd990 *)
bvSub rcx (bvVar rcx) (bvVar L0x7fffffffd990);
(* sub    0x68(%rsp),%r8                           #! EA = L0x7fffffffd998 *)
bvSub r8 (bvVar r8) (bvVar L0x7fffffffd998);
(* sub    0x70(%rsp),%r9                           #! EA = L0x7fffffffd9a0 *)
bvSub r9 (bvVar r9) (bvVar L0x7fffffffd9a0);
(* mov    %rsi,0xa0(%rsp)                          #! EA = L0x7fffffffd9d0 *)
bvAssign L0x7fffffffd9d0 (bvVar rsi);
(* mov    %rdx,0xa8(%rsp)                          #! EA = L0x7fffffffd9d8 *)
bvAssign L0x7fffffffd9d8 (bvVar rdx);
(* mov    %rcx,0xb0(%rsp)                          #! EA = L0x7fffffffd9e0 *)
bvAssign L0x7fffffffd9e0 (bvVar rcx);
(* mov    %r8,0xb8(%rsp)                           #! EA = L0x7fffffffd9e8 *)
bvAssign L0x7fffffffd9e8 (bvVar r8);
(* mov    %r9,0xc0(%rsp)                           #! EA = L0x7fffffffd9f0 *)
bvAssign L0x7fffffffd9f0 (bvVar r9);
(* mov    0x78(%rdi),%rsi                          #! EA = L0x7fffffffdb08 *)
bvAssign rsi (bvVar L0x7fffffffdb08);
(* mov    0x80(%rdi),%rdx                          #! EA = L0x7fffffffdb10 *)
bvAssign rdx (bvVar L0x7fffffffdb10);
(* mov    0x88(%rdi),%rcx                          #! EA = L0x7fffffffdb18 *)
bvAssign rcx (bvVar L0x7fffffffdb18);
(* mov    0x90(%rdi),%r8                           #! EA = L0x7fffffffdb20 *)
bvAssign r8 (bvVar L0x7fffffffdb20);
(* mov    0x98(%rdi),%r9                           #! EA = L0x7fffffffdb28 *)
bvAssign r9 (bvVar L0x7fffffffdb28);
(* mov    %rsi,%rax *)
bvAssign rax (bvVar rsi);
(* mov    %rdx,%r10 *)
bvAssign r10 (bvVar rdx);
(* mov    %rcx,%r11 *)
bvAssign r11 (bvVar rcx);
(* mov    %r8,%r12 *)
bvAssign r12 (bvVar r8);
(* mov    %r9,%r13 *)
bvAssign r13 (bvVar r9);
(* add    0x201fc7(%rip),%rax        # 0x603160    #! EA = L0x603160 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rax (bvVar L0x603160) (bvVar rax);
(* add    0x201fc8(%rip),%r10        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar L0x603168) (bvVar r10);
(* add    0x201fc1(%rip),%r11        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r11 (bvVar L0x603168) (bvVar r11);
(* add    0x201fba(%rip),%r12        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar L0x603168) (bvVar r12);
(* add    0x201fb3(%rip),%r13        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r13 (bvVar L0x603168) (bvVar r13);
(* add    0xa0(%rdi),%rsi                          #! EA = L0x7fffffffdb30 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar L0x7fffffffdb30) (bvVar rsi);
(* add    0xa8(%rdi),%rdx                          #! EA = L0x7fffffffdb38 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rdx (bvVar L0x7fffffffdb38) (bvVar rdx);
(* add    0xb0(%rdi),%rcx                          #! EA = L0x7fffffffdb40 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar L0x7fffffffdb40) (bvVar rcx);
(* add    0xb8(%rdi),%r8                           #! EA = L0x7fffffffdb48 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar L0x7fffffffdb48) (bvVar r8);
(* add    0xc0(%rdi),%r9                           #! EA = L0x7fffffffdb50 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r9 (bvVar L0x7fffffffdb50) (bvVar r9);
(* sub    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvSub rax (bvVar rax) (bvVar L0x7fffffffdb30);
(* sub    0xa8(%rdi),%r10                          #! EA = L0x7fffffffdb38 *)
bvSub r10 (bvVar r10) (bvVar L0x7fffffffdb38);
(* sub    0xb0(%rdi),%r11                          #! EA = L0x7fffffffdb40 *)
bvSub r11 (bvVar r11) (bvVar L0x7fffffffdb40);
(* sub    0xb8(%rdi),%r12                          #! EA = L0x7fffffffdb48 *)
bvSub r12 (bvVar r12) (bvVar L0x7fffffffdb48);
(* sub    0xc0(%rdi),%r13                          #! EA = L0x7fffffffdb50 *)
bvSub r13 (bvVar r13) (bvVar L0x7fffffffdb50);
(* mov    %rsi,0xc8(%rsp)                          #! EA = L0x7fffffffd9f8 *)
bvAssign L0x7fffffffd9f8 (bvVar rsi);
(* mov    %rdx,0xd0(%rsp)                          #! EA = L0x7fffffffda00 *)
bvAssign L0x7fffffffda00 (bvVar rdx);
(* mov    %rcx,0xd8(%rsp)                          #! EA = L0x7fffffffda08 *)
bvAssign L0x7fffffffda08 (bvVar rcx);
(* mov    %r8,0xe0(%rsp)                           #! EA = L0x7fffffffda10 *)
bvAssign L0x7fffffffda10 (bvVar r8);
(* mov    %r9,0xe8(%rsp)                           #! EA = L0x7fffffffda18 *)
bvAssign L0x7fffffffda18 (bvVar r9);
(* mov    %rax,0xf0(%rsp)                          #! EA = L0x7fffffffda20 *)
bvAssign L0x7fffffffda20 (bvVar rax);
(* mov    %r10,0xf8(%rsp)                          #! EA = L0x7fffffffda28 *)
bvAssign L0x7fffffffda28 (bvVar r10);
(* mov    %r11,0x100(%rsp)                         #! EA = L0x7fffffffda30 *)
bvAssign L0x7fffffffda30 (bvVar r11);
(* mov    %r12,0x108(%rsp)                         #! EA = L0x7fffffffda38 *)
bvAssign L0x7fffffffda38 (bvVar r12);
(* mov    %r13,0x110(%rsp)                         #! EA = L0x7fffffffda40 *)
bvAssign L0x7fffffffda40 (bvVar r13);
(* mov    0xe0(%rsp),%rsi                          #! EA = L0x7fffffffda10 *)
bvAssign rsi (bvVar L0x7fffffffda10);
(* imul   $0x13,%rsi,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rsi);
(* mov    %rax,0x118(%rsp)                         #! EA = L0x7fffffffda48 *)
bvAssign L0x7fffffffda48 (bvVar rax);
(* mulq   0x38(%rsp)                               #! EA = L0x7fffffffd968 *)
bvMulf rdx rax (bvVar L0x7fffffffd968) (bvVar rax);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    0xe8(%rsp),%rdx                          #! EA = L0x7fffffffda18 *)
bvAssign rdx (bvVar L0x7fffffffda18);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mov    %rax,0x120(%rsp)                         #! EA = L0x7fffffffda50 *)
bvAssign L0x7fffffffda50 (bvVar rax);
(* mulq   0x30(%rsp)                               #! EA = L0x7fffffffd960 *)
bvMulf rdx rax (bvVar L0x7fffffffd960) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xc8(%rsp),%rax                          #! EA = L0x7fffffffd9f8 *)
bvAssign rax (bvVar L0x7fffffffd9f8);
(* mulq   0x28(%rsp)                               #! EA = L0x7fffffffd958 *)
bvMulf rdx rax (bvVar L0x7fffffffd958) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xc8(%rsp),%rax                          #! EA = L0x7fffffffd9f8 *)
bvAssign rax (bvVar L0x7fffffffd9f8);
(* mulq   0x30(%rsp)                               #! EA = L0x7fffffffd960 *)
bvMulf rdx rax (bvVar L0x7fffffffd960) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0xc8(%rsp),%rax                          #! EA = L0x7fffffffd9f8 *)
bvAssign rax (bvVar L0x7fffffffd9f8);
(* mulq   0x38(%rsp)                               #! EA = L0x7fffffffd968 *)
bvMulf rdx rax (bvVar L0x7fffffffd968) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    0xc8(%rsp),%rax                          #! EA = L0x7fffffffd9f8 *)
bvAssign rax (bvVar L0x7fffffffd9f8);
(* mulq   0x40(%rsp)                               #! EA = L0x7fffffffd970 *)
bvMulf rdx rax (bvVar L0x7fffffffd970) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    0xc8(%rsp),%rax                          #! EA = L0x7fffffffd9f8 *)
bvAssign rax (bvVar L0x7fffffffd9f8);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    0xd0(%rsp),%rax                          #! EA = L0x7fffffffda00 *)
bvAssign rax (bvVar L0x7fffffffda00);
(* mulq   0x28(%rsp)                               #! EA = L0x7fffffffd958 *)
bvMulf rdx rax (bvVar L0x7fffffffd958) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0xd0(%rsp),%rax                          #! EA = L0x7fffffffda00 *)
bvAssign rax (bvVar L0x7fffffffda00);
(* mulq   0x30(%rsp)                               #! EA = L0x7fffffffd960 *)
bvMulf rdx rax (bvVar L0x7fffffffd960) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xd0(%rsp),%rax                          #! EA = L0x7fffffffda00 *)
bvAssign rax (bvVar L0x7fffffffda00);
(* mulq   0x38(%rsp)                               #! EA = L0x7fffffffd968 *)
bvMulf rdx rax (bvVar L0x7fffffffd968) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0xd0(%rsp),%rax                          #! EA = L0x7fffffffda00 *)
bvAssign rax (bvVar L0x7fffffffda00);
(* mulq   0x40(%rsp)                               #! EA = L0x7fffffffd970 *)
bvMulf rdx rax (bvVar L0x7fffffffd970) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0xd0(%rsp),%rdx                          #! EA = L0x7fffffffda00 *)
bvAssign rdx (bvVar L0x7fffffffda00);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xd8(%rsp),%rax                          #! EA = L0x7fffffffda08 *)
bvAssign rax (bvVar L0x7fffffffda08);
(* mulq   0x28(%rsp)                               #! EA = L0x7fffffffd958 *)
bvMulf rdx rax (bvVar L0x7fffffffd958) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xd8(%rsp),%rax                          #! EA = L0x7fffffffda08 *)
bvAssign rax (bvVar L0x7fffffffda08);
(* mulq   0x30(%rsp)                               #! EA = L0x7fffffffd960 *)
bvMulf rdx rax (bvVar L0x7fffffffd960) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0xd8(%rsp),%rax                          #! EA = L0x7fffffffda08 *)
bvAssign rax (bvVar L0x7fffffffda08);
(* mulq   0x38(%rsp)                               #! EA = L0x7fffffffd968 *)
bvMulf rdx rax (bvVar L0x7fffffffd968) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0xd8(%rsp),%rdx                          #! EA = L0x7fffffffda08 *)
bvAssign rdx (bvVar L0x7fffffffda08);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x40(%rsp)                               #! EA = L0x7fffffffd970 *)
bvMulf rdx rax (bvVar L0x7fffffffd970) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xd8(%rsp),%rdx                          #! EA = L0x7fffffffda08 *)
bvAssign rdx (bvVar L0x7fffffffda08);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0xe0(%rsp),%rax                          #! EA = L0x7fffffffda10 *)
bvAssign rax (bvVar L0x7fffffffda10);
(* mulq   0x28(%rsp)                               #! EA = L0x7fffffffd958 *)
bvMulf rdx rax (bvVar L0x7fffffffd958) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0xe0(%rsp),%rax                          #! EA = L0x7fffffffda10 *)
bvAssign rax (bvVar L0x7fffffffda10);
(* mulq   0x30(%rsp)                               #! EA = L0x7fffffffd960 *)
bvMulf rdx rax (bvVar L0x7fffffffd960) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x118(%rsp),%rax                         #! EA = L0x7fffffffda48 *)
bvAssign rax (bvVar L0x7fffffffda48);
(* mulq   0x40(%rsp)                               #! EA = L0x7fffffffd970 *)
bvMulf rdx rax (bvVar L0x7fffffffd970) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x118(%rsp),%rax                         #! EA = L0x7fffffffda48 *)
bvAssign rax (bvVar L0x7fffffffda48);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xe8(%rsp),%rax                          #! EA = L0x7fffffffda18 *)
bvAssign rax (bvVar L0x7fffffffda18);
(* mulq   0x28(%rsp)                               #! EA = L0x7fffffffd958 *)
bvMulf rdx rax (bvVar L0x7fffffffd958) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x120(%rsp),%rax                         #! EA = L0x7fffffffda50 *)
bvAssign rax (bvVar L0x7fffffffda50);
(* mulq   0x38(%rsp)                               #! EA = L0x7fffffffd968 *)
bvMulf rdx rax (bvVar L0x7fffffffd968) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x120(%rsp),%rax                         #! EA = L0x7fffffffda50 *)
bvAssign rax (bvVar L0x7fffffffda50);
(* mulq   0x40(%rsp)                               #! EA = L0x7fffffffd970 *)
bvMulf rdx rax (bvVar L0x7fffffffd970) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x120(%rsp),%rax                         #! EA = L0x7fffffffda50 *)
bvAssign rax (bvVar L0x7fffffffda50);
(* mulq   0x48(%rsp)                               #! EA = L0x7fffffffd978 *)
bvMulf rdx rax (bvVar L0x7fffffffd978) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x201cff(%rip),%rdx        # 0x603150    #! EA = L0x603150 *)
bvAssign rdx (bvVar L0x603150);
(* shld   $0xd,%rsi,%rcx *)
(* NOTE: merge 'shld $0xd,%rsi,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx rsi (bvVar rcx) (bvVar rsi) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
(* shld   $0xd,%r8,%r9 *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rdx,%r8' *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
(* add    %rcx,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rcx) (bvVar r8);
(* shld   $0xd,%r10,%r11 *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rdx,%r10' *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
(* add    %r9,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
(* shld   $0xd,%r12,%r13 *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rdx,%r12' *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* and    %rdx,%r12 *)
(* NOTE: merged, see above *)
(* add    %r11,%r12 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
(* shld   $0xd,%r14,%r15 *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rdx,%r14' *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* and    %rdx,%r14 *)
(* NOTE: merged, see above *)
(* add    %r13,%r14 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
(* imul   $0x13,%r15,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar r15);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* mov    %rsi,%rcx *)
bvAssign rcx (bvVar rsi);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r8,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r8) (bvVar rcx);
(* mov    %rcx,%r8 *)
bvAssign r8 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r8' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
bvAssign rsi (bvVar tmp0);
(* add    %r10,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r10) (bvVar rcx);
(* mov    %rcx,%r9 *)
bvAssign r9 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r9' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
bvAssign r8 (bvVar tmp1);
(* add    %r12,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r12) (bvVar rcx);
(* mov    %rcx,%rax *)
bvAssign rax (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rax' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r9 *)
(* NOTE: merged, see above *)
bvAssign r9 (bvVar tmp0);
(* add    %r14,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r14) (bvVar rcx);
(* mov    %rcx,%r10 *)
bvAssign r10 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r10' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rax *)
(* NOTE: merged, see above *)
bvAssign rax (bvVar tmp1);
(* imul   $0x13,%rcx,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar rcx);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
bvAssign r10 (bvVar tmp0);
(* mov    %rsi,0x28(%rsp)                          #! EA = L0x7fffffffd958 *)
bvAssign L0x7fffffffd958 (bvVar rsi);
(* mov    %r8,0x30(%rsp)                           #! EA = L0x7fffffffd960 *)
bvAssign L0x7fffffffd960 (bvVar r8);
(* mov    %r9,0x38(%rsp)                           #! EA = L0x7fffffffd968 *)
bvAssign L0x7fffffffd968 (bvVar r9);
(* mov    %rax,0x40(%rsp)                          #! EA = L0x7fffffffd970 *)
bvAssign L0x7fffffffd970 (bvVar rax);
(* mov    %r10,0x48(%rsp)                          #! EA = L0x7fffffffd978 *)
bvAssign L0x7fffffffd978 (bvVar r10);
(* mov    0x108(%rsp),%rsi                         #! EA = L0x7fffffffda38 *)
bvAssign rsi (bvVar L0x7fffffffda38);
(* imul   $0x13,%rsi,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rsi);
(* mov    %rax,0xc8(%rsp)                          #! EA = L0x7fffffffd9f8 *)
bvAssign L0x7fffffffd9f8 (bvVar rax);
(* mulq   0x10(%rsp)                               #! EA = L0x7fffffffd940 *)
bvMulf rdx rax (bvVar L0x7fffffffd940) (bvVar rax);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    0x110(%rsp),%rdx                         #! EA = L0x7fffffffda40 *)
bvAssign rdx (bvVar L0x7fffffffda40);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mov    %rax,0xd0(%rsp)                          #! EA = L0x7fffffffda00 *)
bvAssign L0x7fffffffda00 (bvVar rax);
(* mulq   0x8(%rsp)                                #! EA = L0x7fffffffd938 *)
bvMulf rdx rax (bvVar L0x7fffffffd938) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xf0(%rsp),%rax                          #! EA = L0x7fffffffda20 *)
bvAssign rax (bvVar L0x7fffffffda20);
(* mulq   (%rsp)                                   #! EA = L0x7fffffffd930 *)
bvMulf rdx rax (bvVar L0x7fffffffd930) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xf0(%rsp),%rax                          #! EA = L0x7fffffffda20 *)
bvAssign rax (bvVar L0x7fffffffda20);
(* mulq   0x8(%rsp)                                #! EA = L0x7fffffffd938 *)
bvMulf rdx rax (bvVar L0x7fffffffd938) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0xf0(%rsp),%rax                          #! EA = L0x7fffffffda20 *)
bvAssign rax (bvVar L0x7fffffffda20);
(* mulq   0x10(%rsp)                               #! EA = L0x7fffffffd940 *)
bvMulf rdx rax (bvVar L0x7fffffffd940) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    0xf0(%rsp),%rax                          #! EA = L0x7fffffffda20 *)
bvAssign rax (bvVar L0x7fffffffda20);
(* mulq   0x18(%rsp)                               #! EA = L0x7fffffffd948 *)
bvMulf rdx rax (bvVar L0x7fffffffd948) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    0xf0(%rsp),%rax                          #! EA = L0x7fffffffda20 *)
bvAssign rax (bvVar L0x7fffffffda20);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    0xf8(%rsp),%rax                          #! EA = L0x7fffffffda28 *)
bvAssign rax (bvVar L0x7fffffffda28);
(* mulq   (%rsp)                                   #! EA = L0x7fffffffd930 *)
bvMulf rdx rax (bvVar L0x7fffffffd930) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0xf8(%rsp),%rax                          #! EA = L0x7fffffffda28 *)
bvAssign rax (bvVar L0x7fffffffda28);
(* mulq   0x8(%rsp)                                #! EA = L0x7fffffffd938 *)
bvMulf rdx rax (bvVar L0x7fffffffd938) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xf8(%rsp),%rax                          #! EA = L0x7fffffffda28 *)
bvAssign rax (bvVar L0x7fffffffda28);
(* mulq   0x10(%rsp)                               #! EA = L0x7fffffffd940 *)
bvMulf rdx rax (bvVar L0x7fffffffd940) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0xf8(%rsp),%rax                          #! EA = L0x7fffffffda28 *)
bvAssign rax (bvVar L0x7fffffffda28);
(* mulq   0x18(%rsp)                               #! EA = L0x7fffffffd948 *)
bvMulf rdx rax (bvVar L0x7fffffffd948) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0xf8(%rsp),%rdx                          #! EA = L0x7fffffffda28 *)
bvAssign rdx (bvVar L0x7fffffffda28);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x100(%rsp),%rax                         #! EA = L0x7fffffffda30 *)
bvAssign rax (bvVar L0x7fffffffda30);
(* mulq   (%rsp)                                   #! EA = L0x7fffffffd930 *)
bvMulf rdx rax (bvVar L0x7fffffffd930) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x100(%rsp),%rax                         #! EA = L0x7fffffffda30 *)
bvAssign rax (bvVar L0x7fffffffda30);
(* mulq   0x8(%rsp)                                #! EA = L0x7fffffffd938 *)
bvMulf rdx rax (bvVar L0x7fffffffd938) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x100(%rsp),%rax                         #! EA = L0x7fffffffda30 *)
bvAssign rax (bvVar L0x7fffffffda30);
(* mulq   0x10(%rsp)                               #! EA = L0x7fffffffd940 *)
bvMulf rdx rax (bvVar L0x7fffffffd940) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x100(%rsp),%rdx                         #! EA = L0x7fffffffda30 *)
bvAssign rdx (bvVar L0x7fffffffda30);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x18(%rsp)                               #! EA = L0x7fffffffd948 *)
bvMulf rdx rax (bvVar L0x7fffffffd948) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x100(%rsp),%rdx                         #! EA = L0x7fffffffda30 *)
bvAssign rdx (bvVar L0x7fffffffda30);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x108(%rsp),%rax                         #! EA = L0x7fffffffda38 *)
bvAssign rax (bvVar L0x7fffffffda38);
(* mulq   (%rsp)                                   #! EA = L0x7fffffffd930 *)
bvMulf rdx rax (bvVar L0x7fffffffd930) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x108(%rsp),%rax                         #! EA = L0x7fffffffda38 *)
bvAssign rax (bvVar L0x7fffffffda38);
(* mulq   0x8(%rsp)                                #! EA = L0x7fffffffd938 *)
bvMulf rdx rax (bvVar L0x7fffffffd938) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0xc8(%rsp),%rax                          #! EA = L0x7fffffffd9f8 *)
bvAssign rax (bvVar L0x7fffffffd9f8);
(* mulq   0x18(%rsp)                               #! EA = L0x7fffffffd948 *)
bvMulf rdx rax (bvVar L0x7fffffffd948) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0xc8(%rsp),%rax                          #! EA = L0x7fffffffd9f8 *)
bvAssign rax (bvVar L0x7fffffffd9f8);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x110(%rsp),%rax                         #! EA = L0x7fffffffda40 *)
bvAssign rax (bvVar L0x7fffffffda40);
(* mulq   (%rsp)                                   #! EA = L0x7fffffffd930 *)
bvMulf rdx rax (bvVar L0x7fffffffd930) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0xd0(%rsp),%rax                          #! EA = L0x7fffffffda00 *)
bvAssign rax (bvVar L0x7fffffffda00);
(* mulq   0x10(%rsp)                               #! EA = L0x7fffffffd940 *)
bvMulf rdx rax (bvVar L0x7fffffffd940) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0xd0(%rsp),%rax                          #! EA = L0x7fffffffda00 *)
bvAssign rax (bvVar L0x7fffffffda00);
(* mulq   0x18(%rsp)                               #! EA = L0x7fffffffd948 *)
bvMulf rdx rax (bvVar L0x7fffffffd948) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xd0(%rsp),%rax                          #! EA = L0x7fffffffda00 *)
bvAssign rax (bvVar L0x7fffffffda00);
(* mulq   0x20(%rsp)                               #! EA = L0x7fffffffd950 *)
bvMulf rdx rax (bvVar L0x7fffffffd950) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x201a65(%rip),%rdx        # 0x603150    #! EA = L0x603150 *)
bvAssign rdx (bvVar L0x603150);
(* shld   $0xd,%rsi,%rcx *)
(* NOTE: merge 'shld $0xd,%rsi,%rcx' with 'and %rdx,%rsi *)
bvConcatShl rcx rsi (bvVar rcx) (bvVar rsi) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
(* shld   $0xd,%r8,%r9 *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rdx,%r8 *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
(* add    %rcx,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rcx) (bvVar r8);
(* shld   $0xd,%r10,%r11 *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rdx,%r10 *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
(* add    %r9,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
(* shld   $0xd,%r12,%r13 *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rdx,%r12 *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* and    %rdx,%r12 *)
(* NOTE: merged, see above *)
(* add    %r11,%r12 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
(* shld   $0xd,%r14,%r15 *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rdx,%r14 *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* and    %rdx,%r14 *)
(* NOTE: merged, see above *)
(* add    %r13,%r14 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
(* imul   $0x13,%r15,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar r15);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* mov    %rsi,%rcx *)
bvAssign rcx (bvVar rsi);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r8,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r8) (bvVar rcx);
(* mov    %rcx,%r8 *)
bvAssign r8 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r8' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
bvAssign rsi (bvVar tmp0);
(* add    %r10,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r10) (bvVar rcx);
(* mov    %rcx,%r9 *)
bvAssign r9 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r9' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
bvAssign r8 (bvVar tmp1);
(* add    %r12,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r12) (bvVar rcx);
(* mov    %rcx,%rax *)
bvAssign rax (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rax' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r9 *)
(* NOTE: merged, see above *)
bvAssign r9 (bvVar tmp0);
(* add    %r14,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r14) (bvVar rcx);
(* mov    %rcx,%r10 *)
bvAssign r10 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r10' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rax *)
(* NOTE: merged, see above *)
bvAssign rax (bvVar tmp1);
(* imul   $0x13,%rcx,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar rcx);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
bvAssign r10 (bvVar tmp0);
(* mov    %rsi,%rdx *)
bvAssign rdx (bvVar rsi);
(* mov    %r8,%rcx *)
bvAssign rcx (bvVar r8);
(* mov    %r9,%r11 *)
bvAssign r11 (bvVar r9);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %r10,%r13 *)
bvAssign r13 (bvVar r10);
(* add    0x2019df(%rip),%rdx        # 0x603160    #! EA = L0x603160 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rdx (bvVar L0x603160) (bvVar rdx);
(* add    0x2019e0(%rip),%rcx        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar L0x603168) (bvVar rcx);
(* add    0x2019d9(%rip),%r11        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r11 (bvVar L0x603168) (bvVar r11);
(* add    0x2019d2(%rip),%r12        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar L0x603168) (bvVar r12);
(* add    0x2019cb(%rip),%r13        # 0x603168    #! EA = L0x603168 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r13 (bvVar L0x603168) (bvVar r13);
(* add    0x28(%rsp),%rsi                          #! EA = L0x7fffffffd958 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar L0x7fffffffd958) (bvVar rsi);
(* add    0x30(%rsp),%r8                           #! EA = L0x7fffffffd960 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar L0x7fffffffd960) (bvVar r8);
(* add    0x38(%rsp),%r9                           #! EA = L0x7fffffffd968 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r9 (bvVar L0x7fffffffd968) (bvVar r9);
(* add    0x40(%rsp),%rax                          #! EA = L0x7fffffffd970 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rax (bvVar L0x7fffffffd970) (bvVar rax);
(* add    0x48(%rsp),%r10                          #! EA = L0x7fffffffd978 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar L0x7fffffffd978) (bvVar r10);
(* sub    0x28(%rsp),%rdx                          #! EA = L0x7fffffffd958 *)
bvSub rdx (bvVar rdx) (bvVar L0x7fffffffd958);
(* sub    0x30(%rsp),%rcx                          #! EA = L0x7fffffffd960 *)
bvSub rcx (bvVar rcx) (bvVar L0x7fffffffd960);
(* sub    0x38(%rsp),%r11                          #! EA = L0x7fffffffd968 *)
bvSub r11 (bvVar r11) (bvVar L0x7fffffffd968);
(* sub    0x40(%rsp),%r12                          #! EA = L0x7fffffffd970 *)
bvSub r12 (bvVar r12) (bvVar L0x7fffffffd970);
(* sub    0x48(%rsp),%r13                          #! EA = L0x7fffffffd978 *)
bvSub r13 (bvVar r13) (bvVar L0x7fffffffd978);
(* mov    %rsi,0x78(%rdi)                          #! EA = L0x7fffffffdb08 *)
bvAssign L0x7fffffffdb08 (bvVar rsi);
(* mov    %r8,0x80(%rdi)                           #! EA = L0x7fffffffdb10 *)
bvAssign L0x7fffffffdb10 (bvVar r8);
(* mov    %r9,0x88(%rdi)                           #! EA = L0x7fffffffdb18 *)
bvAssign L0x7fffffffdb18 (bvVar r9);
(* mov    %rax,0x90(%rdi)                          #! EA = L0x7fffffffdb20 *)
bvAssign L0x7fffffffdb20 (bvVar rax);
(* mov    %r10,0x98(%rdi)                          #! EA = L0x7fffffffdb28 *)
bvAssign L0x7fffffffdb28 (bvVar r10);
(* mov    %rdx,0xa0(%rdi)                          #! EA = L0x7fffffffdb30 *)
bvAssign L0x7fffffffdb30 (bvVar rdx);
(* mov    %rcx,0xa8(%rdi)                          #! EA = L0x7fffffffdb38 *)
bvAssign L0x7fffffffdb38 (bvVar rcx);
(* mov    %r11,0xb0(%rdi)                          #! EA = L0x7fffffffdb40 *)
bvAssign L0x7fffffffdb40 (bvVar r11);
(* mov    %r12,0xb8(%rdi)                          #! EA = L0x7fffffffdb48 *)
bvAssign L0x7fffffffdb48 (bvVar r12);
(* mov    %r13,0xc0(%rdi)                          #! EA = L0x7fffffffdb50 *)
bvAssign L0x7fffffffdb50 (bvVar r13);
(* mov    0x78(%rdi),%rax                          #! EA = L0x7fffffffdb08 *)
bvAssign rax (bvVar L0x7fffffffdb08);
(* mulq   0x78(%rdi)                               #! EA = L0x7fffffffdb08 *)
bvMulf rdx rax (bvVar L0x7fffffffdb08) (bvVar rax);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    0x78(%rdi),%rax                          #! EA = L0x7fffffffdb08 *)
bvAssign rax (bvVar L0x7fffffffdb08);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x80(%rdi)                               #! EA = L0x7fffffffdb10 *)
bvMulf rdx rax (bvVar L0x7fffffffdb10) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0x78(%rdi),%rax                          #! EA = L0x7fffffffdb08 *)
bvAssign rax (bvVar L0x7fffffffdb08);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x88(%rdi)                               #! EA = L0x7fffffffdb18 *)
bvMulf rdx rax (bvVar L0x7fffffffdb18) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    0x78(%rdi),%rax                          #! EA = L0x7fffffffdb08 *)
bvAssign rax (bvVar L0x7fffffffdb08);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x90(%rdi)                               #! EA = L0x7fffffffdb20 *)
bvMulf rdx rax (bvVar L0x7fffffffdb20) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    0x78(%rdi),%rax                          #! EA = L0x7fffffffdb08 *)
bvAssign rax (bvVar L0x7fffffffdb08);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x98(%rdi)                               #! EA = L0x7fffffffdb28 *)
bvMulf rdx rax (bvVar L0x7fffffffdb28) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    0x80(%rdi),%rax                          #! EA = L0x7fffffffdb10 *)
bvAssign rax (bvVar L0x7fffffffdb10);
(* mulq   0x80(%rdi)                               #! EA = L0x7fffffffdb10 *)
bvMulf rdx rax (bvVar L0x7fffffffdb10) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x80(%rdi),%rax                          #! EA = L0x7fffffffdb10 *)
bvAssign rax (bvVar L0x7fffffffdb10);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x88(%rdi)                               #! EA = L0x7fffffffdb18 *)
bvMulf rdx rax (bvVar L0x7fffffffdb18) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x80(%rdi),%rax                          #! EA = L0x7fffffffdb10 *)
bvAssign rax (bvVar L0x7fffffffdb10);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x90(%rdi)                               #! EA = L0x7fffffffdb20 *)
bvMulf rdx rax (bvVar L0x7fffffffdb20) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x80(%rdi),%rdx                          #! EA = L0x7fffffffdb10 *)
bvAssign rdx (bvVar L0x7fffffffdb10);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x98(%rdi)                               #! EA = L0x7fffffffdb28 *)
bvMulf rdx rax (bvVar L0x7fffffffdb28) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x88(%rdi),%rax                          #! EA = L0x7fffffffdb18 *)
bvAssign rax (bvVar L0x7fffffffdb18);
(* mulq   0x88(%rdi)                               #! EA = L0x7fffffffdb18 *)
bvMulf rdx rax (bvVar L0x7fffffffdb18) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x88(%rdi),%rdx                          #! EA = L0x7fffffffdb18 *)
bvAssign rdx (bvVar L0x7fffffffdb18);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x90(%rdi)                               #! EA = L0x7fffffffdb20 *)
bvMulf rdx rax (bvVar L0x7fffffffdb20) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x88(%rdi),%rdx                          #! EA = L0x7fffffffdb18 *)
bvAssign rdx (bvVar L0x7fffffffdb18);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x98(%rdi)                               #! EA = L0x7fffffffdb28 *)
bvMulf rdx rax (bvVar L0x7fffffffdb28) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x90(%rdi),%rdx                          #! EA = L0x7fffffffdb20 *)
bvAssign rdx (bvVar L0x7fffffffdb20);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x90(%rdi)                               #! EA = L0x7fffffffdb20 *)
bvMulf rdx rax (bvVar L0x7fffffffdb20) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x90(%rdi),%rdx                          #! EA = L0x7fffffffdb20 *)
bvAssign rdx (bvVar L0x7fffffffdb20);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x98(%rdi)                               #! EA = L0x7fffffffdb28 *)
bvMulf rdx rax (bvVar L0x7fffffffdb28) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x98(%rdi),%rdx                          #! EA = L0x7fffffffdb28 *)
bvAssign rdx (bvVar L0x7fffffffdb28);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x98(%rdi)                               #! EA = L0x7fffffffdb28 *)
bvMulf rdx rax (bvVar L0x7fffffffdb28) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x2017f3(%rip),%rdx        # 0x603150    #! EA = L0x603150 *)
bvAssign rdx (bvVar L0x603150);
(* shld   $0xd,%rsi,%rcx *)
(* NOTE: merge 'shld $0xd,%rsi,%rcx' with 'and %rdx,%rsi *)
bvConcatShl rcx rsi (bvVar rcx) (bvVar rsi) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
(* shld   $0xd,%r8,%r9 *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rdx,%r8 *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
(* add    %rcx,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rcx) (bvVar r8);
(* shld   $0xd,%r10,%r11 *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rdx,%r10 *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
(* add    %r9,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
(* shld   $0xd,%r12,%r13 *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rdx,%r12 *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* and    %rdx,%r12 *)
(* NOTE: merged, see above *)
(* add    %r11,%r12 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
(* shld   $0xd,%r14,%r15 *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rdx,%r14 *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* and    %rdx,%r14 *)
(* NOTE: merged, see above *)
(* add    %r13,%r14 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
(* imul   $0x13,%r15,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar r15);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* mov    %rsi,%rcx *)
bvAssign rcx (bvVar rsi);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r8,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r8) (bvVar rcx);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
bvAssign rsi (bvVar tmp);
(* mov    %rcx,%r8 *)
bvAssign r8 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r8' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r10,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r10) (bvVar rcx);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
bvAssign r8 (bvVar tmp);
(* mov    %rcx,%r9 *)
bvAssign r9 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r9' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r12,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r12) (bvVar rcx);
(* and    %rdx,%r9 *)
(* NOTE: merged, see above *)
bvAssign r9 (bvVar tmp);
(* mov    %rcx,%rax *)
bvAssign rax (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rax' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r14,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r14) (bvVar rcx);
(* and    %rdx,%rax *)
(* NOTE: merged, see above *)
bvAssign rax (bvVar tmp);
(* mov    %rcx,%r10 *)
bvAssign r10 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r10' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* imul   $0x13,%rcx,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar rcx);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
bvAssign r10 (bvVar tmp);
(* mov    %rsi,0x78(%rdi)                          #! EA = L0x7fffffffdb08 *)
bvAssign L0x7fffffffdb08 (bvVar rsi);
(* mov    %r8,0x80(%rdi)                           #! EA = L0x7fffffffdb10 *)
bvAssign L0x7fffffffdb10 (bvVar r8);
(* mov    %r9,0x88(%rdi)                           #! EA = L0x7fffffffdb18 *)
bvAssign L0x7fffffffdb18 (bvVar r9);
(* mov    %rax,0x90(%rdi)                          #! EA = L0x7fffffffdb20 *)
bvAssign L0x7fffffffdb20 (bvVar rax);
(* mov    %r10,0x98(%rdi)                          #! EA = L0x7fffffffdb28 *)
bvAssign L0x7fffffffdb28 (bvVar r10);
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* mulq   0xa0(%rdi)                               #! EA = L0x7fffffffdb30 *)
bvMulf rdx rax (bvVar L0x7fffffffdb30) (bvVar rax);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0xa8(%rdi)                               #! EA = L0x7fffffffdb38 *)
bvMulf rdx rax (bvVar L0x7fffffffdb38) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0xb0(%rdi)                               #! EA = L0x7fffffffdb40 *)
bvMulf rdx rax (bvVar L0x7fffffffdb40) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0xb8(%rdi)                               #! EA = L0x7fffffffdb48 *)
bvMulf rdx rax (bvVar L0x7fffffffdb48) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0xc0(%rdi)                               #! EA = L0x7fffffffdb50 *)
bvMulf rdx rax (bvVar L0x7fffffffdb50) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    0xa8(%rdi),%rax                          #! EA = L0x7fffffffdb38 *)
bvAssign rax (bvVar L0x7fffffffdb38);
(* mulq   0xa8(%rdi)                               #! EA = L0x7fffffffdb38 *)
bvMulf rdx rax (bvVar L0x7fffffffdb38) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xa8(%rdi),%rax                          #! EA = L0x7fffffffdb38 *)
bvAssign rax (bvVar L0x7fffffffdb38);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0xb0(%rdi)                               #! EA = L0x7fffffffdb40 *)
bvMulf rdx rax (bvVar L0x7fffffffdb40) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0xa8(%rdi),%rax                          #! EA = L0x7fffffffdb38 *)
bvAssign rax (bvVar L0x7fffffffdb38);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0xb8(%rdi)                               #! EA = L0x7fffffffdb48 *)
bvMulf rdx rax (bvVar L0x7fffffffdb48) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0xa8(%rdi),%rdx                          #! EA = L0x7fffffffdb38 *)
bvAssign rdx (bvVar L0x7fffffffdb38);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0xc0(%rdi)                               #! EA = L0x7fffffffdb50 *)
bvMulf rdx rax (bvVar L0x7fffffffdb50) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xb0(%rdi),%rax                          #! EA = L0x7fffffffdb40 *)
bvAssign rax (bvVar L0x7fffffffdb40);
(* mulq   0xb0(%rdi)                               #! EA = L0x7fffffffdb40 *)
bvMulf rdx rax (bvVar L0x7fffffffdb40) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0xb0(%rdi),%rdx                          #! EA = L0x7fffffffdb40 *)
bvAssign rdx (bvVar L0x7fffffffdb40);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0xb8(%rdi)                               #! EA = L0x7fffffffdb48 *)
bvMulf rdx rax (bvVar L0x7fffffffdb48) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xb0(%rdi),%rdx                          #! EA = L0x7fffffffdb40 *)
bvAssign rdx (bvVar L0x7fffffffdb40);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0xc0(%rdi)                               #! EA = L0x7fffffffdb50 *)
bvMulf rdx rax (bvVar L0x7fffffffdb50) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0xb8(%rdi),%rdx                          #! EA = L0x7fffffffdb48 *)
bvAssign rdx (bvVar L0x7fffffffdb48);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0xb8(%rdi)                               #! EA = L0x7fffffffdb48 *)
bvMulf rdx rax (bvVar L0x7fffffffdb48) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0xb8(%rdi),%rdx                          #! EA = L0x7fffffffdb48 *)
bvAssign rdx (bvVar L0x7fffffffdb48);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0xc0(%rdi)                               #! EA = L0x7fffffffdb50 *)
bvMulf rdx rax (bvVar L0x7fffffffdb50) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xc0(%rdi),%rdx                          #! EA = L0x7fffffffdb50 *)
bvAssign rdx (bvVar L0x7fffffffdb50);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0xc0(%rdi)                               #! EA = L0x7fffffffdb50 *)
bvMulf rdx rax (bvVar L0x7fffffffdb50) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x2015f6(%rip),%rdx        # 0x603150    #! EA = L0x603150 *)
bvAssign rdx (bvVar L0x603150);
(* shld   $0xd,%rsi,%rcx *)
(* NOTE: merge 'shld $0xd,%rsi,%rcx' with 'and %rdx,%rsi *)
bvConcatShl rcx rsi (bvVar rcx) (bvVar rsi) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
(* shld   $0xd,%r8,%r9 *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rdx,%r8 *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
(* add    %rcx,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rcx) (bvVar r8);
(* shld   $0xd,%r10,%r11 *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rdx,%r10 *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
(* add    %r9,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
(* shld   $0xd,%r12,%r13 *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rdx,%r12 *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* and    %rdx,%r12 *)
(* NOTE: merged, see above *)
(* add    %r11,%r12 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
(* shld   $0xd,%r14,%r15 *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rdx,%r14 *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* and    %rdx,%r14 *)
(* NOTE: merged, see above *)
(* add    %r13,%r14 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
(* imul   $0x13,%r15,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar r15);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* mov    %rsi,%rcx *)
bvAssign rcx (bvVar rsi);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r8,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r8) (bvVar rcx);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
bvAssign rsi (bvVar tmp);
(* mov    %rcx,%r8 *)
bvAssign r8 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r8' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r10,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r10) (bvVar rcx);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
bvAssign r8 (bvVar tmp);
(* mov    %rcx,%r9 *)
bvAssign r9 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r9' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r12,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r12) (bvVar rcx);
(* and    %rdx,%r9 *)
(* NOTE: merged, see above *)
bvAssign r9 (bvVar tmp);
(* mov    %rcx,%rax *)
bvAssign rax (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rax' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r14,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r14) (bvVar rcx);
(* and    %rdx,%rax *)
(* NOTE: merged, see above *)
bvAssign rax (bvVar tmp);
(* mov    %rcx,%r10 *)
bvAssign r10 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r10' *)
bvConcatShl rcx tmp (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* imul   $0x13,%rcx,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar rcx);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
bvAssign r10 (bvVar tmp);
(* mov    %rsi,0xa0(%rdi)                          #! EA = L0x7fffffffdb30 *)
bvAssign L0x7fffffffdb30 (bvVar rsi);
(* mov    %r8,0xa8(%rdi)                           #! EA = L0x7fffffffdb38 *)
bvAssign L0x7fffffffdb38 (bvVar r8);
(* mov    %r9,0xb0(%rdi)                           #! EA = L0x7fffffffdb40 *)
bvAssign L0x7fffffffdb40 (bvVar r9);
(* mov    %rax,0xb8(%rdi)                          #! EA = L0x7fffffffdb48 *)
bvAssign L0x7fffffffdb48 (bvVar rax);
(* mov    %r10,0xc0(%rdi)                          #! EA = L0x7fffffffdb50 *)
bvAssign L0x7fffffffdb50 (bvVar r10);
(* mov    0xb8(%rdi),%rsi                          #! EA = L0x7fffffffdb48 *)
bvAssign rsi (bvVar L0x7fffffffdb48);
(* imul   $0x13,%rsi,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rsi);
(* mov    %rax,(%rsp)                              #! EA = L0x7fffffffd930 *)
bvAssign L0x7fffffffd930 (bvVar rax);
(* mulq   0x10(%rdi)                               #! EA = L0x7fffffffdaa0 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa0) (bvVar rax);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    0xc0(%rdi),%rdx                          #! EA = L0x7fffffffdb50 *)
bvAssign rdx (bvVar L0x7fffffffdb50);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mov    %rax,0x8(%rsp)                           #! EA = L0x7fffffffd938 *)
bvAssign L0x7fffffffd938 (bvVar rax);
(* mulq   0x8(%rdi)                                #! EA = L0x7fffffffda98 *)
bvMulf rdx rax (bvVar L0x7fffffffda98) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* mulq   (%rdi)                                   #! EA = L0x7fffffffda90 *)
bvMulf rdx rax (bvVar L0x7fffffffda90) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* mulq   0x8(%rdi)                                #! EA = L0x7fffffffda98 *)
bvMulf rdx rax (bvVar L0x7fffffffda98) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* mulq   0x10(%rdi)                               #! EA = L0x7fffffffdaa0 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa0) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* mulq   0x18(%rdi)                               #! EA = L0x7fffffffdaa8 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa8) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    0xa0(%rdi),%rax                          #! EA = L0x7fffffffdb30 *)
bvAssign rax (bvVar L0x7fffffffdb30);
(* mulq   0x20(%rdi)                               #! EA = L0x7fffffffdab0 *)
bvMulf rdx rax (bvVar L0x7fffffffdab0) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    0xa8(%rdi),%rax                          #! EA = L0x7fffffffdb38 *)
bvAssign rax (bvVar L0x7fffffffdb38);
(* mulq   (%rdi)                                   #! EA = L0x7fffffffda90 *)
bvMulf rdx rax (bvVar L0x7fffffffda90) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0xa8(%rdi),%rax                          #! EA = L0x7fffffffdb38 *)
bvAssign rax (bvVar L0x7fffffffdb38);
(* mulq   0x8(%rdi)                                #! EA = L0x7fffffffda98 *)
bvMulf rdx rax (bvVar L0x7fffffffda98) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xa8(%rdi),%rax                          #! EA = L0x7fffffffdb38 *)
bvAssign rax (bvVar L0x7fffffffdb38);
(* mulq   0x10(%rdi)                               #! EA = L0x7fffffffdaa0 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa0) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0xa8(%rdi),%rax                          #! EA = L0x7fffffffdb38 *)
bvAssign rax (bvVar L0x7fffffffdb38);
(* mulq   0x18(%rdi)                               #! EA = L0x7fffffffdaa8 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa8) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0xa8(%rdi),%rdx                          #! EA = L0x7fffffffdb38 *)
bvAssign rdx (bvVar L0x7fffffffdb38);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x20(%rdi)                               #! EA = L0x7fffffffdab0 *)
bvMulf rdx rax (bvVar L0x7fffffffdab0) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xb0(%rdi),%rax                          #! EA = L0x7fffffffdb40 *)
bvAssign rax (bvVar L0x7fffffffdb40);
(* mulq   (%rdi)                                   #! EA = L0x7fffffffda90 *)
bvMulf rdx rax (bvVar L0x7fffffffda90) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xb0(%rdi),%rax                          #! EA = L0x7fffffffdb40 *)
bvAssign rax (bvVar L0x7fffffffdb40);
(* mulq   0x8(%rdi)                                #! EA = L0x7fffffffda98 *)
bvMulf rdx rax (bvVar L0x7fffffffda98) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0xb0(%rdi),%rax                          #! EA = L0x7fffffffdb40 *)
bvAssign rax (bvVar L0x7fffffffdb40);
(* mulq   0x10(%rdi)                               #! EA = L0x7fffffffdaa0 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa0) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0xb0(%rdi),%rdx                          #! EA = L0x7fffffffdb40 *)
bvAssign rdx (bvVar L0x7fffffffdb40);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x18(%rdi)                               #! EA = L0x7fffffffdaa8 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa8) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0xb0(%rdi),%rdx                          #! EA = L0x7fffffffdb40 *)
bvAssign rdx (bvVar L0x7fffffffdb40);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x20(%rdi)                               #! EA = L0x7fffffffdab0 *)
bvMulf rdx rax (bvVar L0x7fffffffdab0) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0xb8(%rdi),%rax                          #! EA = L0x7fffffffdb48 *)
bvAssign rax (bvVar L0x7fffffffdb48);
(* mulq   (%rdi)                                   #! EA = L0x7fffffffda90 *)
bvMulf rdx rax (bvVar L0x7fffffffda90) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0xb8(%rdi),%rax                          #! EA = L0x7fffffffdb48 *)
bvAssign rax (bvVar L0x7fffffffdb48);
(* mulq   0x8(%rdi)                                #! EA = L0x7fffffffda98 *)
bvMulf rdx rax (bvVar L0x7fffffffda98) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* mulq   0x18(%rdi)                               #! EA = L0x7fffffffdaa8 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa8) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* mulq   0x20(%rdi)                               #! EA = L0x7fffffffdab0 *)
bvMulf rdx rax (bvVar L0x7fffffffdab0) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0xc0(%rdi),%rax                          #! EA = L0x7fffffffdb50 *)
bvAssign rax (bvVar L0x7fffffffdb50);
(* mulq   (%rdi)                                   #! EA = L0x7fffffffda90 *)
bvMulf rdx rax (bvVar L0x7fffffffda90) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0x10(%rdi)                               #! EA = L0x7fffffffdaa0 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa0) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0x18(%rdi)                               #! EA = L0x7fffffffdaa8 *)
bvMulf rdx rax (bvVar L0x7fffffffdaa8) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0x20(%rdi)                               #! EA = L0x7fffffffdab0 *)
bvMulf rdx rax (bvVar L0x7fffffffdab0) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x201397(%rip),%rdx        # 0x603150    #! EA = L0x603150 *)
bvAssign rdx (bvVar L0x603150);
(* shld   $0xd,%rsi,%rcx *)
(* NOTE: merge 'shld $0xd,%rsi,%rcx' with 'and %rdx,%rsi *)
bvConcatShl rcx rsi (bvVar rcx) (bvVar rsi) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
(* shld   $0xd,%r8,%r9 *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rdx,%r8 *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
(* add    %rcx,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rcx) (bvVar r8);
(* shld   $0xd,%r10,%r11 *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rdx,%r10 *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
(* add    %r9,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
(* shld   $0xd,%r12,%r13 *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rdx,%r12 *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* and    %rdx,%r12 *)
(* NOTE: merged, see above *)
(* add    %r11,%r12 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
(* shld   $0xd,%r14,%r15 *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rdx,%r14 *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* and    %rdx,%r14 *)
(* NOTE: merged, see above *)
(* add    %r13,%r14 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
(* imul   $0x13,%r15,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar r15);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* mov    %rsi,%rcx *)
bvAssign rcx (bvVar rsi);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r8,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r8) (bvVar rcx);
(* mov    %rcx,%r8 *)
bvAssign r8 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r8' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
bvAssign rsi (bvVar tmp0);
(* add    %r10,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r10) (bvVar rcx);
(* mov    %rcx,%r9 *)
bvAssign r9 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r9' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
bvAssign r8 (bvVar tmp1);
(* add    %r12,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r12) (bvVar rcx);
(* mov    %rcx,%rax *)
bvAssign rax (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rax' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r9 *)
(* NOTE: merged, see above *)
bvAssign r9 (bvVar tmp0);
(* add    %r14,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r14) (bvVar rcx);
(* mov    %rcx,%r10 *)
bvAssign r10 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r10' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rax *)
(* NOTE: merged, see above *)
bvAssign rax (bvVar tmp1);
(* imul   $0x13,%rcx,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar rcx);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
bvAssign r10 (bvVar tmp0);
(* mov    %rsi,0xa0(%rdi)                          #! EA = L0x7fffffffdb30 *)
bvAssign L0x7fffffffdb30 (bvVar rsi);
(* mov    %r8,0xa8(%rdi)                           #! EA = L0x7fffffffdb38 *)
bvAssign L0x7fffffffdb38 (bvVar r8);
(* mov    %r9,0xb0(%rdi)                           #! EA = L0x7fffffffdb40 *)
bvAssign L0x7fffffffdb40 (bvVar r9);
(* mov    %rax,0xb8(%rdi)                          #! EA = L0x7fffffffdb48 *)
bvAssign L0x7fffffffdb48 (bvVar rax);
(* mov    %r10,0xc0(%rdi)                          #! EA = L0x7fffffffdb50 *)
bvAssign L0x7fffffffdb50 (bvVar r10);
(* mov    0x90(%rsp),%rsi                          #! EA = L0x7fffffffd9c0 *)
bvAssign rsi (bvVar L0x7fffffffd9c0);
(* imul   $0x13,%rsi,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rsi);
(* mov    %rax,(%rsp)                              #! EA = L0x7fffffffd930 *)
bvAssign L0x7fffffffd930 (bvVar rax);
(* mulq   0x60(%rsp)                               #! EA = L0x7fffffffd990 *)
bvMulf rdx rax (bvVar L0x7fffffffd990) (bvVar rax);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    0x98(%rsp),%rdx                          #! EA = L0x7fffffffd9c8 *)
bvAssign rdx (bvVar L0x7fffffffd9c8);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mov    %rax,0x8(%rsp)                           #! EA = L0x7fffffffd938 *)
bvAssign L0x7fffffffd938 (bvVar rax);
(* mulq   0x58(%rsp)                               #! EA = L0x7fffffffd988 *)
bvMulf rdx rax (bvVar L0x7fffffffd988) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x78(%rsp),%rax                          #! EA = L0x7fffffffd9a8 *)
bvAssign rax (bvVar L0x7fffffffd9a8);
(* mulq   0x50(%rsp)                               #! EA = L0x7fffffffd980 *)
bvMulf rdx rax (bvVar L0x7fffffffd980) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x78(%rsp),%rax                          #! EA = L0x7fffffffd9a8 *)
bvAssign rax (bvVar L0x7fffffffd9a8);
(* mulq   0x58(%rsp)                               #! EA = L0x7fffffffd988 *)
bvMulf rdx rax (bvVar L0x7fffffffd988) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0x78(%rsp),%rax                          #! EA = L0x7fffffffd9a8 *)
bvAssign rax (bvVar L0x7fffffffd9a8);
(* mulq   0x60(%rsp)                               #! EA = L0x7fffffffd990 *)
bvMulf rdx rax (bvVar L0x7fffffffd990) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    0x78(%rsp),%rax                          #! EA = L0x7fffffffd9a8 *)
bvAssign rax (bvVar L0x7fffffffd9a8);
(* mulq   0x68(%rsp)                               #! EA = L0x7fffffffd998 *)
bvMulf rdx rax (bvVar L0x7fffffffd998) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    0x78(%rsp),%rax                          #! EA = L0x7fffffffd9a8 *)
bvAssign rax (bvVar L0x7fffffffd9a8);
(* mulq   0x70(%rsp)                               #! EA = L0x7fffffffd9a0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9a0) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    0x80(%rsp),%rax                          #! EA = L0x7fffffffd9b0 *)
bvAssign rax (bvVar L0x7fffffffd9b0);
(* mulq   0x50(%rsp)                               #! EA = L0x7fffffffd980 *)
bvMulf rdx rax (bvVar L0x7fffffffd980) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x80(%rsp),%rax                          #! EA = L0x7fffffffd9b0 *)
bvAssign rax (bvVar L0x7fffffffd9b0);
(* mulq   0x58(%rsp)                               #! EA = L0x7fffffffd988 *)
bvMulf rdx rax (bvVar L0x7fffffffd988) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x80(%rsp),%rax                          #! EA = L0x7fffffffd9b0 *)
bvAssign rax (bvVar L0x7fffffffd9b0);
(* mulq   0x60(%rsp)                               #! EA = L0x7fffffffd990 *)
bvMulf rdx rax (bvVar L0x7fffffffd990) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x80(%rsp),%rax                          #! EA = L0x7fffffffd9b0 *)
bvAssign rax (bvVar L0x7fffffffd9b0);
(* mulq   0x68(%rsp)                               #! EA = L0x7fffffffd998 *)
bvMulf rdx rax (bvVar L0x7fffffffd998) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x80(%rsp),%rdx                          #! EA = L0x7fffffffd9b0 *)
bvAssign rdx (bvVar L0x7fffffffd9b0);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x70(%rsp)                               #! EA = L0x7fffffffd9a0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9a0) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x88(%rsp),%rax                          #! EA = L0x7fffffffd9b8 *)
bvAssign rax (bvVar L0x7fffffffd9b8);
(* mulq   0x50(%rsp)                               #! EA = L0x7fffffffd980 *)
bvMulf rdx rax (bvVar L0x7fffffffd980) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x88(%rsp),%rax                          #! EA = L0x7fffffffd9b8 *)
bvAssign rax (bvVar L0x7fffffffd9b8);
(* mulq   0x58(%rsp)                               #! EA = L0x7fffffffd988 *)
bvMulf rdx rax (bvVar L0x7fffffffd988) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x88(%rsp),%rax                          #! EA = L0x7fffffffd9b8 *)
bvAssign rax (bvVar L0x7fffffffd9b8);
(* mulq   0x60(%rsp)                               #! EA = L0x7fffffffd990 *)
bvMulf rdx rax (bvVar L0x7fffffffd990) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x88(%rsp),%rdx                          #! EA = L0x7fffffffd9b8 *)
bvAssign rdx (bvVar L0x7fffffffd9b8);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x68(%rsp)                               #! EA = L0x7fffffffd998 *)
bvMulf rdx rax (bvVar L0x7fffffffd998) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x88(%rsp),%rdx                          #! EA = L0x7fffffffd9b8 *)
bvAssign rdx (bvVar L0x7fffffffd9b8);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x70(%rsp)                               #! EA = L0x7fffffffd9a0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9a0) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x90(%rsp),%rax                          #! EA = L0x7fffffffd9c0 *)
bvAssign rax (bvVar L0x7fffffffd9c0);
(* mulq   0x50(%rsp)                               #! EA = L0x7fffffffd980 *)
bvMulf rdx rax (bvVar L0x7fffffffd980) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x90(%rsp),%rax                          #! EA = L0x7fffffffd9c0 *)
bvAssign rax (bvVar L0x7fffffffd9c0);
(* mulq   0x58(%rsp)                               #! EA = L0x7fffffffd988 *)
bvMulf rdx rax (bvVar L0x7fffffffd988) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* mulq   0x68(%rsp)                               #! EA = L0x7fffffffd998 *)
bvMulf rdx rax (bvVar L0x7fffffffd998) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* mulq   0x70(%rsp)                               #! EA = L0x7fffffffd9a0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9a0) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x98(%rsp),%rax                          #! EA = L0x7fffffffd9c8 *)
bvAssign rax (bvVar L0x7fffffffd9c8);
(* mulq   0x50(%rsp)                               #! EA = L0x7fffffffd980 *)
bvMulf rdx rax (bvVar L0x7fffffffd980) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0x60(%rsp)                               #! EA = L0x7fffffffd990 *)
bvMulf rdx rax (bvVar L0x7fffffffd990) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0x68(%rsp)                               #! EA = L0x7fffffffd998 *)
bvMulf rdx rax (bvVar L0x7fffffffd998) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0x70(%rsp)                               #! EA = L0x7fffffffd9a0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9a0) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x201115(%rip),%rdx        # 0x603150    #! EA = L0x603150 *)
bvAssign rdx (bvVar L0x603150);
(* shld   $0xd,%rsi,%rcx *)
(* NOTE: merge 'shld $0xd,%rsi,%rcx' with 'and %rdx,%rsi *)
bvConcatShl rcx rsi (bvVar rcx) (bvVar rsi) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
(* shld   $0xd,%r8,%r9 *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rdx,%r8 *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
(* add    %rcx,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rcx) (bvVar r8);
(* shld   $0xd,%r10,%r11 *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rdx,%r10 *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
(* add    %r9,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
(* shld   $0xd,%r12,%r13 *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rdx,%r12 *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* and    %rdx,%r12 *)
(* NOTE: merged, see above *)
(* add    %r11,%r12 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
(* shld   $0xd,%r14,%r15 *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rdx,%r14 *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* and    %rdx,%r14 *)
(* NOTE: merged, see above *)
(* add    %r13,%r14 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
(* imul   $0x13,%r15,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar r15);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* mov    %rsi,%rcx *)
bvAssign rcx (bvVar rsi);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r8,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r8) (bvVar rcx);
(* mov    %rcx,%r8 *)
bvAssign r8 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r8' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
bvAssign rsi (bvVar tmp0);
(* add    %r10,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r10) (bvVar rcx);
(* mov    %rcx,%r9 *)
bvAssign r9 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r9' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
bvAssign r8 (bvVar tmp1);
(* add    %r12,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r12) (bvVar rcx);
(* mov    %rcx,%rax *)
bvAssign rax (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rax' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r9 *)
(* NOTE: merged, see above *)
bvAssign r9 (bvVar tmp0);
(* add    %r14,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r14) (bvVar rcx);
(* mov    %rcx,%r10 *)
bvAssign r10 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r10' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rax *)
(* NOTE: merged, see above *)
bvAssign rax (bvVar tmp1);
(* imul   $0x13,%rcx,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar rcx);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
bvAssign r10 (bvVar tmp0);
(* mov    %rsi,0x28(%rdi)                          #! EA = L0x7fffffffdab8 *)
bvAssign L0x7fffffffdab8 (bvVar rsi);
(* mov    %r8,0x30(%rdi)                           #! EA = L0x7fffffffdac0 *)
bvAssign L0x7fffffffdac0 (bvVar r8);
(* mov    %r9,0x38(%rdi)                           #! EA = L0x7fffffffdac8 *)
bvAssign L0x7fffffffdac8 (bvVar r9);
(* mov    %rax,0x40(%rdi)                          #! EA = L0x7fffffffdad0 *)
bvAssign L0x7fffffffdad0 (bvVar rax);
(* mov    %r10,0x48(%rdi)                          #! EA = L0x7fffffffdad8 *)
bvAssign L0x7fffffffdad8 (bvVar r10);
(* mov    0xa0(%rsp),%rax                          #! EA = L0x7fffffffd9d0 *)
bvAssign rax (bvVar L0x7fffffffd9d0);
(* mulq   0x20107a(%rip)        # 0x603158         #! EA = L0x603158 *)
(* bvMulf rdx rax (bvVar L0x603158) (bvVar rax); *)
(* shr    $0xd,%rax *)
(* bvSplit rax tmp (bvVar rax) (fromNat 13); *)
(* NOTE: combine 'mulq 0x20107a(%rip)' with 'shr $0xd,%rax' *)
bvMulf rdx rax (bvConst (fromPosZ 121666%Z)) (bvVar rax);
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    0xa8(%rsp),%rax                          #! EA = L0x7fffffffd9d8 *)
bvAssign rax (bvVar L0x7fffffffd9d8);
(* mulq   0x201061(%rip)        # 0x603158         #! EA = L0x603158 *)
(* bvMulf rdx rax (bvVar L0x603158) (bvVar rax); *)
(* shr    $0xd,%rax *)
(* bvSplit rax tmp (bvVar rax) (fromNat 13); *)
(* NOTE: combine 'mulq 0x20107a(%rip)' with 'shr $0xd,%rax' *)
bvMulf rdx rax (bvConst (fromPosZ 121666%Z)) (bvVar rax);
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
(* add    %rax,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar rax) (bvVar rcx);
(* mov    %rdx,%r8 *)
bvAssign r8 (bvVar rdx);
(* mov    0xb0(%rsp),%rax                          #! EA = L0x7fffffffd9e0 *)
bvAssign rax (bvVar L0x7fffffffd9e0);
(* mulq   0x201048(%rip)        # 0x603158         #! EA = L0x603158 *)
(* bvMulf rdx rax (bvVar L0x603158) (bvVar rax); *)
(* shr    $0xd,%rax *)
(* bvSplit rax tmp (bvVar rax) (fromNat 13); *)
(* NOTE: combine 'mulq 0x20107a(%rip)' with 'shr $0xd,%rax' *)
bvMulf rdx rax (bvConst (fromPosZ 121666%Z)) (bvVar rax);
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
(* add    %rax,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rax) (bvVar r8);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0xb8(%rsp),%rax                          #! EA = L0x7fffffffd9e8 *)
bvAssign rax (bvVar L0x7fffffffd9e8);
(* mulq   0x20102f(%rip)        # 0x603158         #! EA = L0x603158 *)
(* bvMulf rdx rax (bvVar L0x603158) (bvVar rax); *)
(* shr    $0xd,%rax *)
(* bvSplit rax tmp (bvVar rax) (fromNat 13); *)
(* NOTE: combine 'mulq 0x20107a(%rip)' with 'shr $0xd,%rax' *)
bvMulf rdx rax (bvConst (fromPosZ 121666%Z)) (bvVar rax);
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
(* add    %rax,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r9 (bvVar rax) (bvVar r9);
(* mov    %rdx,%r10 *)
bvAssign r10 (bvVar rdx);
(* mov    0xc0(%rsp),%rax                          #! EA = L0x7fffffffd9f0 *)
bvAssign rax (bvVar L0x7fffffffd9f0);
(* mulq   0x201016(%rip)        # 0x603158         #! EA = L0x603158 *)
(* bvMulf rdx rax (bvVar L0x603158) (bvVar rax); *)
(* shr    $0xd,%rax *)
(* bvSplit rax tmp (bvVar rax) (fromNat 13); *)
(* NOTE: combine 'mulq 0x20107a(%rip)' with 'shr $0xd,%rax' *)
bvMulf rdx rax (bvConst (fromPosZ 121666%Z)) (bvVar rax);
bvConcatShl rdx rax (bvVar rdx) (bvVar rax) (fromNat 13);
(* add    %rax,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar rax) (bvVar r10);
(* imul   $0x13,%rdx,%rdx *)
bvMul rdx (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* add    %rdx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rdx) (bvVar rsi);
(* add    0x50(%rsp),%rsi                          #! EA = L0x7fffffffd980 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar L0x7fffffffd980) (bvVar rsi);
(* add    0x58(%rsp),%rcx                          #! EA = L0x7fffffffd988 *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar L0x7fffffffd988) (bvVar rcx);
(* add    0x60(%rsp),%r8                           #! EA = L0x7fffffffd990 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar L0x7fffffffd990) (bvVar r8);
(* add    0x68(%rsp),%r9                           #! EA = L0x7fffffffd998 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r9 (bvVar L0x7fffffffd998) (bvVar r9);
(* add    0x70(%rsp),%r10                          #! EA = L0x7fffffffd9a0 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar L0x7fffffffd9a0) (bvVar r10);
(* mov    %rsi,0x50(%rdi)                          #! EA = L0x7fffffffdae0 *)
bvAssign L0x7fffffffdae0 (bvVar rsi);
(* mov    %rcx,0x58(%rdi)                          #! EA = L0x7fffffffdae8 *)
bvAssign L0x7fffffffdae8 (bvVar rcx);
(* mov    %r8,0x60(%rdi)                           #! EA = L0x7fffffffdaf0 *)
bvAssign L0x7fffffffdaf0 (bvVar r8);
(* mov    %r9,0x68(%rdi)                           #! EA = L0x7fffffffdaf8 *)
bvAssign L0x7fffffffdaf8 (bvVar r9);
(* mov    %r10,0x70(%rdi)                          #! EA = L0x7fffffffdb00 *)
bvAssign L0x7fffffffdb00 (bvVar r10);
(* mov    0x68(%rdi),%rsi                          #! EA = L0x7fffffffdaf8 *)
bvAssign rsi (bvVar L0x7fffffffdaf8);
(* imul   $0x13,%rsi,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rsi);
(* mov    %rax,(%rsp)                              #! EA = L0x7fffffffd930 *)
bvAssign L0x7fffffffd930 (bvVar rax);
(* mulq   0xb0(%rsp)                               #! EA = L0x7fffffffd9e0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e0) (bvVar rax);
(* mov    %rax,%rsi *)
bvAssign rsi (bvVar rax);
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* mov    0x70(%rdi),%rdx                          #! EA = L0x7fffffffdb00 *)
bvAssign rdx (bvVar L0x7fffffffdb00);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mov    %rax,0x8(%rsp)                           #! EA = L0x7fffffffd938 *)
bvAssign L0x7fffffffd938 (bvVar rax);
(* mulq   0xa8(%rsp)                               #! EA = L0x7fffffffd9d8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d8) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x50(%rdi),%rax                          #! EA = L0x7fffffffdae0 *)
bvAssign rax (bvVar L0x7fffffffdae0);
(* mulq   0xa0(%rsp)                               #! EA = L0x7fffffffd9d0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d0) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x50(%rdi),%rax                          #! EA = L0x7fffffffdae0 *)
bvAssign rax (bvVar L0x7fffffffdae0);
(* mulq   0xa8(%rsp)                               #! EA = L0x7fffffffd9d8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d8) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0x50(%rdi),%rax                          #! EA = L0x7fffffffdae0 *)
bvAssign rax (bvVar L0x7fffffffdae0);
(* mulq   0xb0(%rsp)                               #! EA = L0x7fffffffd9e0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e0) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    0x50(%rdi),%rax                          #! EA = L0x7fffffffdae0 *)
bvAssign rax (bvVar L0x7fffffffdae0);
(* mulq   0xb8(%rsp)                               #! EA = L0x7fffffffd9e8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e8) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    0x50(%rdi),%rax                          #! EA = L0x7fffffffdae0 *)
bvAssign rax (bvVar L0x7fffffffdae0);
(* mulq   0xc0(%rsp)                               #! EA = L0x7fffffffd9f0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9f0) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    0x58(%rdi),%rax                          #! EA = L0x7fffffffdae8 *)
bvAssign rax (bvVar L0x7fffffffdae8);
(* mulq   0xa0(%rsp)                               #! EA = L0x7fffffffd9d0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d0) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x58(%rdi),%rax                          #! EA = L0x7fffffffdae8 *)
bvAssign rax (bvVar L0x7fffffffdae8);
(* mulq   0xa8(%rsp)                               #! EA = L0x7fffffffd9d8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d8) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x58(%rdi),%rax                          #! EA = L0x7fffffffdae8 *)
bvAssign rax (bvVar L0x7fffffffdae8);
(* mulq   0xb0(%rsp)                               #! EA = L0x7fffffffd9e0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e0) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x58(%rdi),%rax                          #! EA = L0x7fffffffdae8 *)
bvAssign rax (bvVar L0x7fffffffdae8);
(* mulq   0xb8(%rsp)                               #! EA = L0x7fffffffd9e8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e8) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x58(%rdi),%rdx                          #! EA = L0x7fffffffdae8 *)
bvAssign rdx (bvVar L0x7fffffffdae8);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0xc0(%rsp)                               #! EA = L0x7fffffffd9f0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9f0) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x60(%rdi),%rax                          #! EA = L0x7fffffffdaf0 *)
bvAssign rax (bvVar L0x7fffffffdaf0);
(* mulq   0xa0(%rsp)                               #! EA = L0x7fffffffd9d0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d0) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x60(%rdi),%rax                          #! EA = L0x7fffffffdaf0 *)
bvAssign rax (bvVar L0x7fffffffdaf0);
(* mulq   0xa8(%rsp)                               #! EA = L0x7fffffffd9d8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d8) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x60(%rdi),%rax                          #! EA = L0x7fffffffdaf0 *)
bvAssign rax (bvVar L0x7fffffffdaf0);
(* mulq   0xb0(%rsp)                               #! EA = L0x7fffffffd9e0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e0) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x60(%rdi),%rdx                          #! EA = L0x7fffffffdaf0 *)
bvAssign rdx (bvVar L0x7fffffffdaf0);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0xb8(%rsp)                               #! EA = L0x7fffffffd9e8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e8) (bvVar rax);
(* add    %rax,%rsi *)
bvAddC carry rsi (bvVar rax) (bvVar rsi);
(* adc    %rdx,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdc rcx (bvVar rdx) (bvVar rcx) carry;
(* mov    0x60(%rdi),%rdx                          #! EA = L0x7fffffffdaf0 *)
bvAssign rdx (bvVar L0x7fffffffdaf0);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0xc0(%rsp)                               #! EA = L0x7fffffffd9f0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9f0) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x68(%rdi),%rax                          #! EA = L0x7fffffffdaf8 *)
bvAssign rax (bvVar L0x7fffffffdaf8);
(* mulq   0xa0(%rsp)                               #! EA = L0x7fffffffd9d0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d0) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x68(%rdi),%rax                          #! EA = L0x7fffffffdaf8 *)
bvAssign rax (bvVar L0x7fffffffdaf8);
(* mulq   0xa8(%rsp)                               #! EA = L0x7fffffffd9d8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d8) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* mulq   0xb8(%rsp)                               #! EA = L0x7fffffffd9e8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e8) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    (%rsp),%rax                              #! EA = L0x7fffffffd930 *)
bvAssign rax (bvVar L0x7fffffffd930);
(* mulq   0xc0(%rsp)                               #! EA = L0x7fffffffd9f0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9f0) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x70(%rdi),%rax                          #! EA = L0x7fffffffdb00 *)
bvAssign rax (bvVar L0x7fffffffdb00);
(* mulq   0xa0(%rsp)                               #! EA = L0x7fffffffd9d0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9d0) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0xb0(%rsp)                               #! EA = L0x7fffffffd9e0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e0) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0xb8(%rsp)                               #! EA = L0x7fffffffd9e8 *)
bvMulf rdx rax (bvVar L0x7fffffffd9e8) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
(* mov    0x8(%rsp),%rax                           #! EA = L0x7fffffffd938 *)
bvAssign rax (bvVar L0x7fffffffd938);
(* mulq   0xc0(%rsp)                               #! EA = L0x7fffffffd9f0 *)
bvMulf rdx rax (bvVar L0x7fffffffd9f0) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
(* mov    0x200dea(%rip),%rdx        # 0x603150    #! EA = L0x603150 *)
bvAssign rdx (bvVar L0x603150);
(* shld   $0xd,%rsi,%rcx *)
(* NOTE: merge 'shld $0xd,%rsi,%rcx' with 'and %rdx,%rsi *)
bvConcatShl rcx rsi (bvVar rcx) (bvVar rsi) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
(* shld   $0xd,%r8,%r9 *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rdx,%r8 *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
(* add    %rcx,%r8 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rcx) (bvVar r8);
(* shld   $0xd,%r10,%r11 *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rdx,%r10 *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
(* add    %r9,%r10 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
(* shld   $0xd,%r12,%r13 *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rdx,%r12 *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* and    %rdx,%r12 *)
(* NOTE: merged, see above *)
(* add    %r11,%r12 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
(* shld   $0xd,%r14,%r15 *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rdx,%r14 *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* and    %rdx,%r14 *)
(* NOTE: merged, see above *)
(* add    %r13,%r14 *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
(* imul   $0x13,%r15,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar r15);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* mov    %rsi,%rcx *)
bvAssign rcx (bvVar rsi);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rsi' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* add    %r8,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r8) (bvVar rcx);
(* mov    %rcx,%r8 *)
bvAssign r8 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r8' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rsi *)
(* NOTE: merged, see above *)
bvAssign rsi (bvVar tmp0);
(* add    %r10,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r10) (bvVar rcx);
(* mov    %rcx,%r9 *)
bvAssign r9 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r9' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r8 *)
(* NOTE: merged, see above *)
bvAssign r8 (bvVar tmp1);
(* add    %r12,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r12) (bvVar rcx);
(* mov    %rcx,%rax *)
bvAssign rax (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%rax' *)
bvConcatShl rcx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%r9 *)
(* NOTE: merged, see above *)
bvAssign r9 (bvVar tmp0);
(* add    %r14,%rcx *)
(* NOTE: ignore carry because it is zero *)
bvAdd rcx (bvVar r14) (bvVar rcx);
(* mov    %rcx,%r10 *)
bvAssign r10 (bvVar rcx);
(* shr    $0x33,%rcx *)
(* NOTE: merge 'shr $0x33,%rcx' with 'and %rdx,%r10' *)
bvConcatShl rcx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rcx) (fromNat 13);
(* and    %rdx,%rax *)
(* NOTE: merged, see above *)
bvAssign rax (bvVar tmp1);
(* imul   $0x13,%rcx,%rcx *)
bvMul rcx (bvConst (fromPosZ 19%Z)) (bvVar rcx);
(* add    %rcx,%rsi *)
(* NOTE: ignore carry because it is zero *)
bvAdd rsi (bvVar rcx) (bvVar rsi);
(* and    %rdx,%r10 *)
(* NOTE: merged, see above *)
bvAssign r10 (bvVar tmp0);
(* mov    %rsi,0x50(%rdi)                          #! EA = L0x7fffffffdae0 *)
bvAssign L0x7fffffffdae0 (bvVar rsi);
(* mov    %r8,0x58(%rdi)                           #! EA = L0x7fffffffdae8 *)
bvAssign L0x7fffffffdae8 (bvVar r8);
(* mov    %r9,0x60(%rdi)                           #! EA = L0x7fffffffdaf0 *)
bvAssign L0x7fffffffdaf0 (bvVar r9);
(* mov    %rax,0x68(%rdi)                          #! EA = L0x7fffffffdaf8 *)
bvAssign L0x7fffffffdaf8 (bvVar rax);
(* mov    %r10,0x70(%rdi)                          #! EA = L0x7fffffffdb00 *)
bvAssign L0x7fffffffdb00 (bvVar r10);

bvAssign x1'0 (bvVar L0x7fffffffda90);
bvAssign x1'1 (bvVar L0x7fffffffda98);
bvAssign x1'2 (bvVar L0x7fffffffdaa0);
bvAssign x1'3 (bvVar L0x7fffffffdaa8);
bvAssign x1'4 (bvVar L0x7fffffffdab0);

bvAssign x2'0 (bvVar L0x7fffffffdab8);
bvAssign x2'1 (bvVar L0x7fffffffdac0);
bvAssign x2'2 (bvVar L0x7fffffffdac8);
bvAssign x2'3 (bvVar L0x7fffffffdad0);
bvAssign x2'4 (bvVar L0x7fffffffdad8);

bvAssign z2'0 (bvVar L0x7fffffffdae0);
bvAssign z2'1 (bvVar L0x7fffffffdae8);
bvAssign z2'2 (bvVar L0x7fffffffdaf0);
bvAssign z2'3 (bvVar L0x7fffffffdaf8);
bvAssign z2'4 (bvVar L0x7fffffffdb00);

bvAssign x3'0 (bvVar L0x7fffffffdb08);
bvAssign x3'1 (bvVar L0x7fffffffdb10);
bvAssign x3'2 (bvVar L0x7fffffffdb18);
bvAssign x3'3 (bvVar L0x7fffffffdb20);
bvAssign x3'4 (bvVar L0x7fffffffdb28);

bvAssign z3'0 (bvVar L0x7fffffffdb30);
bvAssign z3'1 (bvVar L0x7fffffffdb38);
bvAssign z3'2 (bvVar L0x7fffffffdb40);
bvAssign z3'3 (bvVar L0x7fffffffdb48);
bvAssign z3'4 (bvVar L0x7fffffffdb50)

] .

Definition x25519_x86_64_ladderstep_spec :=
  {| spre := check_pre;
     sprog := program;
     spost := x25519_x86_64_ladderstep_post |}.

Definition x25519_x86_64_ladderstep_spec1 :=
  {| spre := check_pre;
     sprog := program;
     spost := x25519_x86_64_ladderstep_post1 |}.

Definition x25519_x86_64_ladderstep_spec2 :=
  {| spre := check_pre;
     sprog := program;
     spost := x25519_x86_64_ladderstep_post2 |}.

Definition x25519_x86_64_ladderstep_spec3 :=
  {| spre := check_pre;
     sprog := program;
     spost := x25519_x86_64_ladderstep_post3 |}.

Definition x25519_x86_64_ladderstep_spec3_1 :=
  {| spre := check_pre;
     sprog := program;
     spost := x25519_x86_64_ladderstep_post3_1 |}.

Definition x25519_x86_64_ladderstep_spec3_2 :=
  {| spre := check_pre;
     sprog := program;
     spost := x25519_x86_64_ladderstep_post3_2 |}.

Lemma valid_x25519_x86_64_ladderstep1 : 
  valid_bvspec (check_inputs, x25519_x86_64_ladderstep_spec1).
Proof.
  time "valid_x25519_x86_64_ladderstep1" verify_bvspec.
Qed.
