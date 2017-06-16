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
Definition radix64 := @limbs 64 .

Definition check_inputs : VS.t :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  a4 := 1004 in
  let  b0 := 2000 in
  let  b1 := 2001 in
  let  b2 := 2002 in
  let  b3 := 2003 in
  let  b4 := 2004 in
  let  t0 := 3000 in
  let  t1 := 3001 in
  let  t2 := 3002 in
  let  t3 := 3003 in
  let  t4 := 3004 in
  VSLemmas.OP.P.of_list [:: a0; a1; a2; a3; a4; b0; b1; b2; b3; b4 ].

Definition check_pre : bexp := 
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  a4 := 1004 in
  let  b0 := 2000 in
  let  b1 := 2001 in
  let  b2 := 2002 in
  let  b3 := 2003 in
  let  b4 := 2004 in
bvrands
  [::
     (bvrvar a0) <=r (bvposz (2^52)%Z);
     (bvrvar a1) <=r (bvposz (2^52)%Z);
     (bvrvar a2) <=r (bvposz (2^52)%Z);
     (bvrvar a3) <=r (bvposz (2^52)%Z);
     (bvrvar a4) <=r (bvposz (2^52)%Z);
     (bvrvar b0) <=r (bvposz (2^52)%Z);
     (bvrvar b1) <=r (bvposz (2^52)%Z);
     (bvrvar b2) <=r (bvposz (2^52)%Z);
     (bvrvar b3) <=r (bvposz (2^52)%Z);
     (bvrvar b4) <=r (bvposz (2^52)%Z)
  ].

Definition x25519_x86_64_mul_post : bexp :=
  let rax := 10 in
  let rbx := 23 in
  let rbp := 26 in
  let rcx := 6 in
  let rdx := 25 in
  let rsi := 5 in
  let r8 := 24 in
  let r9 := 0 in
  let r10 := 18 in
  let r11 := 19 in
  let r12 := 16 in
  let r13 := 17 in
  let r14 := 14 in
  let r15 := 15 in

  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  a4 := 1004 in
  let  b0 := 2000 in
  let  b1 := 2001 in
  let  b2 := 2002 in
  let  b3 := 2003 in
  let  b4 := 2004 in
  let  t0 := 3000 in
  let  t1 := 3001 in
  let  t2 := 3002 in
  let  t3 := 3003 in
  let  t4 := 3004 in
  let  p25519 := (2^255 - 19)%Z in
  bvands2
    [::
       bveEqMod
       (
         (radix51 [::bvevar a0; bvevar a1; bvevar a2; bvevar a3; bvevar a4])
         *e
         (radix51 [::bvevar b0; bvevar b1; bvevar b2; bvevar b3; bvevar b4])
       )

       (
         (radix51 [::bvevar t0; bvevar t1; bvevar t2; bvevar t3; bvevar t4])
       )    

       (
         (bvconst p25519)
       )
    ]
    [::
       (bvrvar t0) <=r (bvposz (2^52)%Z);
       (bvrvar t1) <=r (bvposz (2^52)%Z);
       (bvrvar t2) <=r (bvposz (2^52)%Z);
       (bvrvar t3) <=r (bvposz (2^52)%Z);
       (bvrvar t4) <=r (bvposz (2^52)%Z)
    ] .

Definition program :=
let L0x7fffffffdb50 := 20 in
let L0x7fffffffdb58 := 22 in
let L0x7fffffffdb60 := 3 in
let L0x7fffffffdb68 := 1 in
let L0x7fffffffdb70 := 21 in

let L0x7fffffffdb00 := 4 in
let L0x7fffffffdb08 := 2 in

let L0x603060 := 13 in
let L0x603068 := 9 in
let L0x603070 := 30 in
let L0x603078 := 28 in
let L0x603080 := 8 in

let L0x6030a0 := 29 in
let L0x6030a8 := 27 in
let L0x6030b0 := 7 in
let L0x6030b8 := 12 in
let L0x6030c0 := 31 in

let L0x6030d0 := 11 in

let rax := 10 in
let rbx := 23 in
let rbp := 26 in
let rcx := 6 in
let rdx := 25 in
let rsi := 5 in
let r8 := 24 in
let r9 := 0 in
let r10 := 18 in
let r11 := 19 in
let r12 := 16 in
let r13 := 17 in
let r14 := 14 in
let r15 := 15 in

let carry := 999 in
let tmp   := 998 in
let tmp0  := 997 in
let tmp1  := 996 in

let  a0 := 1000 in
let  a1 := 1001 in
let  a2 := 1002 in
let  a3 := 1003 in
let  a4 := 1004 in
let  b0 := 2000 in
let  b1 := 2001 in
let  b2 := 2002 in
let  b3 := 2003 in
let  b4 := 2004 in
let  t0 := 3000 in
let  t1 := 3001 in
let  t2 := 3002 in
let  t3 := 3003 in
let  t4 := 3004 in

[::

bvAssign L0x603060 (bvVar a0);
bvAssign L0x603068 (bvVar a1);
bvAssign L0x603070 (bvVar a2);
bvAssign L0x603078 (bvVar a3);
bvAssign L0x603080 (bvVar a4);

bvAssign L0x6030a0 (bvVar b0);
bvAssign L0x6030a8 (bvVar b1);
bvAssign L0x6030b0 (bvVar b2);
bvAssign L0x6030b8 (bvVar b3);
bvAssign L0x6030c0 (bvVar b4);

bvAssign L0x6030d0 (bvConst (fromPosZ (2^52 - 1)%Z));

(* mov    0x18(%rsi),%rdx                          #! EA = L0x603078 *)
bvAssign rdx (bvVar L0x603078);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mov    %rax,-0x40(%rsp)                         #! EA = L0x7fffffffdb08 *)
bvAssign L0x7fffffffdb08 (bvVar rax);
(* mulq   0x10(%rcx)                               #! EA = L0x6030b0 *)
bvMulf rdx rax (bvVar L0x6030b0) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign r8 (bvVar rax);
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* mov    0x20(%rsi),%rdx                          #! EA = L0x603080 *)
bvAssign rdx (bvVar L0x603080);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mov    %rax,-0x48(%rsp)                         #! EA = L0x7fffffffdb00 *)
bvAssign L0x7fffffffdb00 (bvVar rax);
(* mulq   0x8(%rcx)                                #! EA = L0x6030a8 *)
bvMulf rdx rax (bvVar L0x6030a8) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* bvAdcC carry r9 (bvVar rdx) (bvVar r9) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* mulq   (%rcx)                                   #! EA = L0x6030a0 *)
bvMulf rdx rax (bvVar L0x6030a0) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* bvAdcC carry r9 (bvVar rdx) (bvVar r9) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* mulq   0x8(%rcx)                                #! EA = L0x6030a8 *)
bvMulf rdx rax (bvVar L0x6030a8) (bvVar rax);
(* mov    %rax,%r10 *)
bvAssign r10 (bvVar rax);
(* mov    %rdx,%r11 *)
bvAssign r11 (bvVar rdx);
(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* mulq   0x10(%rcx)                               #! EA = L0x6030b0 *)
bvMulf rdx rax (bvVar L0x6030b0) (bvVar rax);
(* mov    %rax,%r12 *)
bvAssign r12 (bvVar rax);
(* mov    %rdx,%r13 *)
bvAssign r13 (bvVar rdx);
(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* mulq   0x18(%rcx)                               #! EA = L0x6030b8 *)
bvMulf rdx rax (bvVar L0x6030b8) (bvVar rax);
(* mov    %rax,%r14 *)
bvAssign r14 (bvVar rax);
(* mov    %rdx,%r15 *)
bvAssign r15 (bvVar rdx);
(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* mulq   0x20(%rcx)                               #! EA = L0x6030c0 *)
bvMulf rdx rax (bvVar L0x6030c0) (bvVar rax);
(* mov    %rax,%rbx *)
bvAssign rbx (bvVar rax);
(* mov    %rdx,%rbp *)
bvAssign rbp (bvVar rdx);
(* mov    0x8(%rsi),%rax                           #! EA = L0x603068 *)
bvAssign rax (bvVar L0x603068);
(* mulq   (%rcx)                                   #! EA = L0x6030a0 *)
bvMulf rdx rax (bvVar L0x6030a0) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* bvAdcC carry r11 (bvVar rdx) (bvVar r11) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x8(%rsi),%rax                           #! EA = L0x603068 *)
bvAssign rax (bvVar L0x603068);
(* mulq   0x8(%rcx)                                #! EA = L0x6030a8 *)
bvMulf rdx rax (bvVar L0x6030a8) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* bvAdcC carry r13 (bvVar rdx) (bvVar r13) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x8(%rsi),%rax                           #! EA = L0x603068 *)
bvAssign rax (bvVar L0x603068);
(* mulq   0x10(%rcx)                               #! EA = L0x6030b0 *)
bvMulf rdx rax (bvVar L0x6030b0) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* bvAdcC carry r15 (bvVar rdx) (bvVar r15) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x8(%rsi),%rax                           #! EA = L0x603068 *)
bvAssign rax (bvVar L0x603068);
(* mulq   0x18(%rcx)                               #! EA = L0x6030b8 *)
bvMulf rdx rax (bvVar L0x6030b8) (bvVar rax);
(* add    %rax,%rbx *)
bvAddC carry rbx (bvVar rax) (bvVar rbx);
(* adc    %rdx,%rbp *)
(* bvAdcC carry rbp (bvVar rdx) (bvVar rbp) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc rbp (bvVar rdx) (bvVar rbp) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x8(%rsi),%rdx                           #! EA = L0x603068 *)
bvAssign rdx (bvVar L0x603068);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x20(%rcx)                               #! EA = L0x6030c0 *)
bvMulf rdx rax (bvVar L0x6030c0) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* bvAdcC carry r9 (bvVar rdx) (bvVar r9) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x10(%rsi),%rax                          #! EA = L0x603070 *)
bvAssign rax (bvVar L0x603070);
(* mulq   (%rcx)                                   #! EA = L0x6030a0 *)
bvMulf rdx rax (bvVar L0x6030a0) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* bvAdcC carry r13 (bvVar rdx) (bvVar r13) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x10(%rsi),%rax                          #! EA = L0x603070 *)
bvAssign rax (bvVar L0x603070);
(* mulq   0x8(%rcx)                                #! EA = L0x6030a8 *)
bvMulf rdx rax (bvVar L0x6030a8) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* bvAdcC carry r15 (bvVar rdx) (bvVar r15) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x10(%rsi),%rax                          #! EA = L0x603070 *)
bvAssign rax (bvVar L0x603070);
(* mulq   0x10(%rcx)                               #! EA = L0x6030b0 *)
bvMulf rdx rax (bvVar L0x6030b0) (bvVar rax);
(* add    %rax,%rbx *)
bvAddC carry rbx (bvVar rax) (bvVar rbx);
(* adc    %rdx,%rbp *)
(* bvAdcC carry rbp (bvVar rdx) (bvVar rbp) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc rbp (bvVar rdx) (bvVar rbp) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x10(%rsi),%rdx                          #! EA = L0x603070 *)
bvAssign rdx (bvVar L0x603070);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x18(%rcx)                               #! EA = L0x6030b8 *)
bvMulf rdx rax (bvVar L0x6030b8) (bvVar rax);
(* add    %rax,%r8 *)
bvAddC carry r8 (bvVar rax) (bvVar r8);
(* adc    %rdx,%r9 *)
(* bvAdcC carry r9 (bvVar rdx) (bvVar r9) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r9 (bvVar rdx) (bvVar r9) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x10(%rsi),%rdx                          #! EA = L0x603070 *)
bvAssign rdx (bvVar L0x603070);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x20(%rcx)                               #! EA = L0x6030c0 *)
bvMulf rdx rax (bvVar L0x6030c0) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* bvAdcC carry r11 (bvVar rdx) (bvVar r11) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x18(%rsi),%rax                          #! EA = L0x603078 *)
bvAssign rax (bvVar L0x603078);
(* mulq   (%rcx)                                   #! EA = L0x6030a0 *)
bvMulf rdx rax (bvVar L0x6030a0) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* bvAdcC carry r15 (bvVar rdx) (bvVar r15) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x18(%rsi),%rax                          #! EA = L0x603078 *)
bvAssign rax (bvVar L0x603078);
(* mulq   0x8(%rcx)                                #! EA = L0x6030a8 *)
bvMulf rdx rax (bvVar L0x6030a8) (bvVar rax);
(* add    %rax,%rbx *)
bvAddC carry rbx (bvVar rax) (bvVar rbx);
(* adc    %rdx,%rbp *)
(* bvAdcC carry rbp (bvVar rdx) (bvVar rbp) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc rbp (bvVar rdx) (bvVar rbp) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    -0x40(%rsp),%rax                         #! EA = L0x7fffffffdb08 *)
bvAssign rax (bvVar L0x7fffffffdb08);
(* mulq   0x18(%rcx)                               #! EA = L0x6030b8 *)
bvMulf rdx rax (bvVar L0x6030b8) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* bvAdcC carry r11 (bvVar rdx) (bvVar r11) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    -0x40(%rsp),%rax                         #! EA = L0x7fffffffdb08 *)
bvAssign rax (bvVar L0x7fffffffdb08);
(* mulq   0x20(%rcx)                               #! EA = L0x6030c0 *)
bvMulf rdx rax (bvVar L0x6030c0) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* bvAdcC carry r13 (bvVar rdx) (bvVar r13) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x20(%rsi),%rax                          #! EA = L0x603080 *)
bvAssign rax (bvVar L0x603080);
(* mulq   (%rcx)                                   #! EA = L0x6030a0 *)
bvMulf rdx rax (bvVar L0x6030a0) (bvVar rax);
(* add    %rax,%rbx *)
bvAddC carry rbx (bvVar rax) (bvVar rbx);
(* adc    %rdx,%rbp *)
(* bvAdcC carry rbp (bvVar rdx) (bvVar rbp) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc rbp (bvVar rdx) (bvVar rbp) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    -0x48(%rsp),%rax                         #! EA = L0x7fffffffdb00 *)
bvAssign rax (bvVar L0x7fffffffdb00);
(* mulq   0x10(%rcx)                               #! EA = L0x6030b0 *)
bvMulf rdx rax (bvVar L0x6030b0) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry r10 (bvVar rax) (bvVar r10);
(* adc    %rdx,%r11 *)
(* bvAdcC carry r11 (bvVar rdx) (bvVar r11) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r11 (bvVar rdx) (bvVar r11) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    -0x48(%rsp),%rax                         #! EA = L0x7fffffffdb00 *)
bvAssign rax (bvVar L0x7fffffffdb00);
(* mulq   0x18(%rcx)                               #! EA = L0x6030b8 *)
bvMulf rdx rax (bvVar L0x6030b8) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry r12 (bvVar rax) (bvVar r12);
(* adc    %rdx,%r13 *)
(* bvAdcC carry r13 (bvVar rdx) (bvVar r13) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvVar rdx) (bvVar r13) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    -0x48(%rsp),%rax                         #! EA = L0x7fffffffdb00 *)
bvAssign rax (bvVar L0x7fffffffdb00);
(* mulq   0x20(%rcx)                               #! EA = L0x6030c0 *)
bvMulf rdx rax (bvVar L0x6030c0) (bvVar rax);
(* add    %rax,%r14 *)
bvAddC carry r14 (bvVar rax) (bvVar r14);
(* adc    %rdx,%r15 *)
(* bvAdcC carry r15 (bvVar rdx) (bvVar r15) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r15 (bvVar rdx) (bvVar r15) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));

(* mov    0x202831(%rip),%rsi        # 0x6030d0    #! EA = L0x6030d0 *)
bvAssign rsi (bvVar L0x6030d0);
(* shld   $0xd,%r8,%r9 *)
(* bvConcatShl r9 tmp (bvVar r9) (bvVar r8) (fromNat 13); *)
(* and    %rsi,%r8 *)
(* bvSplit tmp r8 (bvVar r8) (fromNat 51); *)
(* NOTE: merge 'shld $0xd,%r8,%r9' with 'and %rsi,%r8' *)
bvConcatShl r9 r8 (bvVar r9) (bvVar r8) (fromNat 13);
(* shld   $0xd,%r10,%r11 *)
(* bvConcatShl r11 tmp (bvVar r11) (bvVar r10) (fromNat 13); *)
(* and    %rsi,%r10 *)
(* bvSplit tmp r10 (bvVar r10) (fromNat 51); *)
(* NOTE: merge 'shld $0xd,%r10,%r11' with 'and %rsi,%r10' *)
bvConcatShl r11 r10 (bvVar r11) (bvVar r10) (fromNat 13);
(* add    %r9,%r10 *)
(* bvAddC carry r10 (bvVar r9) (bvVar r10); *)
(* NOTE: ignore carry because it is zero *)
bvAdd r10 (bvVar r9) (bvVar r10);
bvAssign carry (bvConst (fromPosZ 0%Z));
(* shld   $0xd,%r12,%r13 *)
(* bvConcatShl r13 tmp (bvVar r13) (bvVar r12) (fromNat 13); *)
(* and    %rsi,%r12 *)
(* bvSplit tmp r12 (bvVar r12) (fromNat 51); *)
(* NOTE: merge 'shld $0xd,%r12,%r13' with 'and %rsi,%r12' *)
bvConcatShl r13 r12 (bvVar r13) (bvVar r12) (fromNat 13);
(* add    %r11,%r12 *)
(* bvAddC carry r12 (bvVar r11) (bvVar r12); *)
(* NOTE: ignore carry because it is zero *)
bvAdd r12 (bvVar r11) (bvVar r12);
bvAssign carry (bvConst (fromPosZ 0%Z));
(* shld   $0xd,%r14,%r15 *)
(* bvConcatShl r15 tmp (bvVar r15) (bvVar r14) (fromNat 13); *)
(* and    %rsi,%r14 *)
(* bvSplit tmp r14 (bvVar r14) (fromNat 51); *)
(* NOTE: merge 'shld $0xd,%r14,%r15' with 'and %rsi,%r14' *)
bvConcatShl r15 r14 (bvVar r15) (bvVar r14) (fromNat 13);
(* add    %r13,%r14 *)
(* bvAddC carry r14 (bvVar r13) (bvVar r14); *)
(* NOTE: ignore carry because it is zero *)
bvAdd r14 (bvVar r13) (bvVar r14);
bvAssign carry (bvConst (fromPosZ 0%Z));
(* shld   $0xd,%rbx,%rbp *)
(* bvConcatShl rbp tmp (bvVar rbp) (bvVar rbx) (fromNat 13); *)
(* and    %rsi,%rbx *)
(* bvSplit tmp rbx (bvVar rbx) (fromNat 51); *)
(* NOTE: merge 'shld $0xd,%rbx,%rbp' with 'and %rsi,%rbx' *)
bvConcatShl rbp rbx (bvVar rbp) (bvVar rbx) (fromNat 13);
(* add    %r15,%rbx *)
(* bvAddC carry rbx (bvVar r15) (bvVar rbx); *)
(* NOTE: ignore carry because it is zero *)
bvAdd rbx (bvVar r15) (bvVar rbx);
bvAssign carry (bvConst (fromPosZ 0%Z));
(* imul   $0x13,%rbp,%rdx *)
bvMul rdx (bvConst (fromPosZ 19%Z)) (bvVar rbp);
(* add    %rdx,%r8 *)
(* bvAddC carry r8 (bvVar rdx) (bvVar r8); *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rdx) (bvVar r8);
bvAssign carry (bvConst (fromPosZ 0%Z));

(* mov    %r8,%rdx *)
bvAssign rdx (bvVar r8);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and %rsi,%r8' *)
bvConcatShl rdx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* add    %r10,%rdx *)
(* bvAddC carry rdx (bvVar r10) (bvVar rdx); *)
(* NOTE: ignore carry because it is zero *)
bvAdd rdx (bvVar r10) (bvVar rdx);
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    %rdx,%rcx *)
bvAssign rcx (bvVar rdx);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and %rsi,%rcx' *)
bvConcatShl rdx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* and    %rsi,%r8 *)
(* bvSplit tmp r8 (bvVar r8) (fromNat 51); *)
(* NOTE: recover lower 51 bits *)
bvAssign r8 (bvVar tmp0);
(* add    %r12,%rdx *)
(* bvAddC carry rdx (bvVar r12) (bvVar rdx); *)
(* NOTE: ignore carry because it is zero *)
bvAdd rdx (bvVar r12) (bvVar rdx);
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and %rsi,%r9' *)
bvConcatShl rdx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* and    %rsi,%rcx *)
(* bvSplit tmp rcx (bvVar rcx) (fromNat 51); *)
(* NOTE: recover lower 51 bits *)
bvAssign rcx (bvVar tmp1);
(* add    %r14,%rdx *)
(* bvAddC carry rdx (bvVar r14) (bvVar rdx); *)
(* NOTE: ignore carry because it is zero *)
bvAdd rdx (bvVar r14) (bvVar rdx);
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    %rdx,%rax *)
bvAssign rax (bvVar rdx);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and %rsi,%rax' *)
bvConcatShl rdx tmp1 (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* and    %rsi,%r9 *)
(* bvSplit tmp r9 (bvVar r9) (fromNat 51); *)
(* NOTE: recover lower 51 bits *)
bvAssign r9 (bvVar tmp0);
(* add    %rbx,%rdx *)
(* bvAddC carry rdx (bvVar rbx) (bvVar rdx); *)
(* NOTE: ignore carry because it is zero *)
bvAdd rdx (bvVar rbx) (bvVar rdx);
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    %rdx,%r10 *)
bvAssign r10 (bvVar rdx);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and %rsi,%r10' *)
bvConcatShl rdx tmp0 (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* and    %rsi,%rax *)
(* bvSplit tmp rax (bvVar rax) (fromNat 51); *)
(* NOTE: recover lower 51 bits *)
bvAssign rax (bvVar tmp1);
(* imul   $0x13,%rdx,%rdx *)
bvMul rdx (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* add    %rdx,%r8 *)
(* bvAddC carry r8 (bvVar rdx) (bvVar r8); *)
(* NOTE: ignore carry because it is zero *)
bvAdd r8 (bvVar rdx) (bvVar r8);
bvAssign carry (bvConst (fromPosZ 0%Z));
(* and    %rsi,%r10 *)
(* bvSplit tmp r10 (bvVar r10) (fromNat 51); *)
(* NOTE: recover lower 51 bits *)
bvAssign r10 (bvVar tmp0);
(* mov    %r8,(%rdi)                               #! EA = L0x7fffffffdb50 *)
bvAssign L0x7fffffffdb50 (bvVar r8);
(* mov    %rcx,0x8(%rdi)                           #! EA = L0x7fffffffdb58 *)
bvAssign L0x7fffffffdb58 (bvVar rcx);
(* mov    %r9,0x10(%rdi)                           #! EA = L0x7fffffffdb60 *)
bvAssign L0x7fffffffdb60 (bvVar r9);
(* mov    %rax,0x18(%rdi)                          #! EA = L0x7fffffffdb68 *)
bvAssign L0x7fffffffdb68 (bvVar rax);
(* mov    %r10,0x20(%rdi)                          #! EA = L0x7fffffffdb70 *)
bvAssign L0x7fffffffdb70 (bvVar r10);

bvAssign t0 (bvVar L0x7fffffffdb50);
bvAssign t1 (bvVar L0x7fffffffdb58);
bvAssign t2 (bvVar L0x7fffffffdb60);
bvAssign t3 (bvVar L0x7fffffffdb68);
bvAssign t4 (bvVar L0x7fffffffdb70)
         
].

Definition x25519_x86_64_mul_spec :=
  {| spre := check_pre;
     sprog := program;
     spost := x25519_x86_64_mul_post |}.

Lemma valid_x25519_x86_64_mul :
  valid_bvspec (check_inputs, x25519_x86_64_mul_spec).
Proof.
  time "valid_x25519_x86_64_mul" verify_bvspec .
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.
