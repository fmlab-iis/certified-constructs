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
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  a4 := 1004 in
  let  t0 := 3000 in
  let  t1 := 3001 in
  let  t2 := 3002 in
  let  t3 := 3003 in
  let  t4 := 3004 in
  VSLemmas.OP.P.of_list [:: a0; a1; a2; a3; a4 ].

Definition check_pre : bexp := 
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  a4 := 1004 in
bvrands
  [::
     (bvrvar a0) <=r (bvposz (2^52)%Z);
     (bvrvar a1) <=r (bvposz (2^52)%Z);
     (bvrvar a2) <=r (bvposz (2^52)%Z);
     (bvrvar a3) <=r (bvposz (2^52)%Z);
     (bvrvar a4) <=r (bvposz (2^52)%Z)
  ].

Definition x25519_x86_64_mul_post : bexp :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  a4 := 1004 in
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
         (radix51 [::bvevar a0; bvevar a1; bvevar a2; bvevar a3; bvevar a4])
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
let L0x7fffffffdb40 := 1 in
let L0x7fffffffdb48 := 3 in
let L0x7fffffffdb50 := 17 in
let L0x7fffffffdb58 := 18 in
let L0x7fffffffdb60 := 2 in

let L0x603060 := 10 in
let L0x603068 := 8 in
let L0x603070 := 23 in
let L0x603078 := 22 in
let L0x603080 := 7 in

let L0x6030d0 := 9 in

let r9 := 0 in
let rax := 4 in
let rsi := 5 in
let rcx := 6 in
let r14 := 11 in
let r15 := 12 in
let r12 := 13 in
let r13 := 14 in
let r10 := 15 in
let r11 := 16 in
let rbx := 19 in
let r8 := 20 in
let rdx := 21 in

let carry := 999 in
let tmp   := 998 in

let  a0 := 1000 in
let  a1 := 1001 in
let  a2 := 1002 in
let  a3 := 1003 in
let  a4 := 1004 in
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

bvAssign L0x6030d0 (bvConst (fromPosZ (2^52 - 1)%Z));

(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* mulq   (%rsi)                                   #! EA = L0x603060 *)
bvMulf rdx rax (bvVar L0x603060) (bvVar rax);
(* mov    %rax,%rcx *)
bvAssign rcx (bvVar rax);
(* mov    %rdx,%r8 *)
bvAssign r8 (bvVar rdx);
(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x8(%rsi)                                #! EA = L0x603068 *)
bvMulf rdx rax (bvVar L0x603068) (bvVar rax);
(* mov    %rax,%r9 *)
bvAssign r9 (bvVar rax);
(* mov    %rdx,%r10 *)
bvAssign r10 (bvVar rdx);
(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x10(%rsi)                               #! EA = L0x603070 *)
bvMulf rdx rax (bvVar L0x603070) (bvVar rax);
(* mov    %rax,%r11 *)
bvAssign r11 (bvVar rax);
(* mov    %rdx,%r12 *)
bvAssign r12 (bvVar rdx);
(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x18(%rsi)                               #! EA = L0x603078 *)
bvMulf rdx rax (bvVar L0x603078) (bvVar rax);
(* mov    %rax,%r13 *)
bvAssign r13 (bvVar rax);
(* mov    %rdx,%r14 *)
bvAssign r14 (bvVar rdx);
(* mov    (%rsi),%rax                              #! EA = L0x603060 *)
bvAssign rax (bvVar L0x603060);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x20(%rsi)                               #! EA = L0x603080 *)
bvMulf rdx rax (bvVar L0x603080) (bvVar rax);
(* mov    %rax,%r15 *)
bvAssign r15 (bvVar rax);
(* mov    %rdx,%rbx *)
bvAssign rbx (bvVar rdx);
(* mov    0x8(%rsi),%rax                           #! EA = L0x603068 *)
bvAssign rax (bvVar L0x603068);
(* mulq   0x8(%rsi)                                #! EA = L0x603068 *)
bvMulf rdx rax (bvVar L0x603068) (bvVar rax);
(* add    %rax,%r11 *)
bvAddC carry r11 (bvVar rax) (bvVar r11);
(* adc    %rdx,%r12 *)
bvAdcC carry r12 (bvVar rdx) (bvVar r12) carry;
(* mov    0x8(%rsi),%rax                           #! EA = L0x603068 *)
bvAssign rax (bvVar L0x603068);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x10(%rsi)                               #! EA = L0x603070 *)
bvMulf rdx rax (bvVar L0x603070) (bvVar rax);
(* add    %rax,%r13 *)
bvAddC carry r13 (bvVar rax) (bvVar r13);
(* adc    %rdx,%r14 *)
bvAdcC carry r14 (bvVar rdx) (bvVar r14) carry;
(* mov    0x8(%rsi),%rax                           #! EA = L0x603068 *)
bvAssign rax (bvVar L0x603068);
(* shl    %rax *)
bvShl rax (bvVar rax) (fromNat 1);
(* mulq   0x18(%rsi)                               #! EA = L0x603078 *)
bvMulf rdx rax (bvVar L0x603078) (bvVar rax);
(* add    %rax,%r15 *)
bvAddC carry r15 (bvVar rax) (bvVar r15);
(* adc    %rdx,%rbx *)
bvAdcC carry rbx (bvVar rdx) (bvVar rbx) carry;
(* mov    0x8(%rsi),%rdx                           #! EA = L0x603068 *)
bvAssign rdx (bvVar L0x603068);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x20(%rsi)                               #! EA = L0x603080 *)
bvMulf rdx rax (bvVar L0x603080) (bvVar rax);
(* add    %rax,%rcx *)
bvAddC carry rcx (bvVar rax) (bvVar rcx);
(* adc    %rdx,%r8 *)
bvAdcC carry r8 (bvVar rdx) (bvVar r8) carry;
(* mov    0x10(%rsi),%rax                          #! EA = L0x603070 *)
bvAssign rax (bvVar L0x603070);
(* mulq   0x10(%rsi)                               #! EA = L0x603070 *)
bvMulf rdx rax (bvVar L0x603070) (bvVar rax);
(* add    %rax,%r15 *)
bvAddC carry r15 (bvVar rax) (bvVar r15);
(* adc    %rdx,%rbx *)
bvAdcC carry rbx (bvVar rdx) (bvVar rbx) carry;
(* mov    0x10(%rsi),%rdx                          #! EA = L0x603070 *)
bvAssign rdx (bvVar L0x603070);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x18(%rsi)                               #! EA = L0x603078 *)
bvMulf rdx rax (bvVar L0x603078) (bvVar rax);
(* add    %rax,%rcx *)
bvAddC carry rcx (bvVar rax) (bvVar rcx);
(* adc    %rdx,%r8 *)
bvAdcC carry r8 (bvVar rdx) (bvVar r8) carry;
(* mov    0x10(%rsi),%rdx                          #! EA = L0x603070 *)
bvAssign rdx (bvVar L0x603070);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x20(%rsi)                               #! EA = L0x603080 *)
bvMulf rdx rax (bvVar L0x603080) (bvVar rax);
(* add    %rax,%r9 *)
bvAddC carry r9 (bvVar rax) (bvVar r9);
(* adc    %rdx,%r10 *)
bvAdcC carry r10 (bvVar rdx) (bvVar r10) carry;
(* mov    0x18(%rsi),%rdx                          #! EA = L0x603078 *)
bvAssign rdx (bvVar L0x603078);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x18(%rsi)                               #! EA = L0x603078 *)
bvMulf rdx rax (bvVar L0x603078) (bvVar rax);
(* add    %rax,%r9 *)
bvAddC carry r9 (bvVar rax) (bvVar r9);
(* adc    %rdx,%r10 *)
bvAdcC carry r10 (bvVar rdx) (bvVar r10) carry;
(* mov    0x18(%rsi),%rdx                          #! EA = L0x603078 *)
bvAssign rdx (bvVar L0x603078);
(* imul   $0x26,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 38%Z)) (bvVar rdx);
(* mulq   0x20(%rsi)                               #! EA = L0x603080 *)
bvMulf rdx rax (bvVar L0x603080) (bvVar rax);
(* add    %rax,%r11 *)
bvAddC carry r11 (bvVar rax) (bvVar r11);
(* adc    %rdx,%r12 *)
bvAdcC carry r12 (bvVar rdx) (bvVar r12) carry;
(* mov    0x20(%rsi),%rdx                          #! EA = L0x603080 *)
bvAssign rdx (bvVar L0x603080);
(* imul   $0x13,%rdx,%rax *)
bvMul rax (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* mulq   0x20(%rsi)                               #! EA = L0x603080 *)
bvMulf rdx rax (bvVar L0x603080) (bvVar rax);
(* add    %rax,%r13 *)
bvAddC carry r13 (bvVar rax) (bvVar r13);
(* adc    %rdx,%r14 *)
bvAdcC carry r14 (bvVar rdx) (bvVar r14) carry;
(* mov    0x2026da(%rip),%rsi        # 0x6030d0    #! EA = L0x6030d0 *)
bvAssign rsi (bvVar L0x6030d0);
(* shld   $0xd,%rcx,%r8 *)
(* NOTE: merge 'shld $0xd,%rcx,%r8' with 'and %rsi,%rcs' *)
bvConcatShl r8 tmp (bvVar r8) (bvVar rcx) (fromNat 13);
(* and    %rsi,%rcx *)
(* bvSplit tmp rcx (bvVar rcx) (fromNat 51); *)
(* NOTE: see above *)
bvAssign rcx (bvVar tmp);
(* shld   $0xd,%r9,%r10 *)
(* NOTE: merge 'shld $0xd,%r9,%r10' with 'and %rsi,%r9' *)
bvConcatShl r10 tmp (bvVar r10) (bvVar r9) (fromNat 13);
(* and    %rsi,%r9 *)
(* bvSplit tmp r9 (bvVar r9) (fromNat 51); *)
(* NOTE: see above *)
bvAssign r9 (bvVar tmp);
(* add    %r8,%r9 *)
bvAddC carry r9 (bvVar r8) (bvVar r9);
(* shld   $0xd,%r11,%r12 *)
(* NOTE: merge 'shld $0xd,%r11,%12' with 'and %rsi,%r11' *)
bvConcatShl r12 tmp (bvVar r12) (bvVar r11) (fromNat 13);
(* and    %rsi,%r11 *)
(* bvSplit tmp r11 (bvVar r11) (fromNat 51); *)
(* NOTE: see above *)
bvAssign r11 (bvVar tmp);
(* add    %r10,%r11 *)
bvAddC carry r11 (bvVar r10) (bvVar r11);
(* shld   $0xd,%r13,%r14 *)
(* NOTE: merge 'shld $0xd,%r13,%r14' with 'and %rsi,%r13' *)
bvConcatShl r14 tmp (bvVar r14) (bvVar r13) (fromNat 13);
(* and    %rsi,%r13 *)
(* bvSplit tmp r13 (bvVar r13) (fromNat 51); *)
(* NOTE: see above *)
bvAssign r13 (bvVar tmp);
(* add    %r12,%r13 *)
bvAddC carry r13 (bvVar r12) (bvVar r13);
(* shld   $0xd,%r15,%rbx *)
(* NOTE: merge 'shld $0xd,%r15,%rbx' with 'and %rsi,%r15' *)
bvConcatShl rbx tmp (bvVar rbx) (bvVar r15) (fromNat 13);
(* and    %rsi,%r15 *)
(* bvSplit tmp r15 (bvVar r15) (fromNat 51); *)
(* NOTE: see above *)
bvAssign r15 (bvVar tmp);
(* add    %r14,%r15 *)
bvAddC carry r15 (bvVar r14) (bvVar r15);
(* imul   $0x13,%rbx,%rdx *)
bvMul rdx (bvConst (fromPosZ 19%Z)) (bvVar rbx);
(* add    %rdx,%rcx *)
bvAddC carry rcx (bvVar rdx) (bvVar rcx);
(* mov    %rcx,%rdx *)
bvAssign rdx (bvVar rcx);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and '%rsi,%rcx' *)
bvConcatShl rdx rcx (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* add    %r9,%rdx *)
bvAddC carry rdx (bvVar r9) (bvVar rdx);
(* and    %rsi,%rcx *)
(* bvSplit tmp rcx (bvVar rcx) (fromNat 51); *)
(* NOTE: see above *)
(* mov    %rdx,%r8 *)
bvAssign r8 (bvVar rdx);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and '%rsi,%r8' *)
bvConcatShl rdx r8 (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* add    %r11,%rdx *)
bvAddC carry rdx (bvVar r11) (bvVar rdx);
(* and    %rsi,%r8 *)
(* bvSplit tmp r8 (bvVar r8) (fromNat 51); *)
(* NOTE: see above *)
(* mov    %rdx,%r9 *)
bvAssign r9 (bvVar rdx);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and '%rsi,%r9' *)
bvConcatShl rdx r9 (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* add    %r13,%rdx *)
bvAddC carry rdx (bvVar r13) (bvVar rdx);
(* and    %rsi,%r9 *)
(* bvSplit tmp r9 (bvVar r9) (fromNat 51); *)
(* NOTE: see above *)
(* mov    %rdx,%rax *)
bvAssign rax (bvVar rdx);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and '%rsi,%rax' *)
bvConcatShl rdx rax (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* add    %r15,%rdx *)
bvAddC carry rdx (bvVar r15) (bvVar rdx);
(* and    %rsi,%rax *)
(* bvSplit tmp rax (bvVar rax) (fromNat 51); *)
(* NOTE: see above *)
(* mov    %rdx,%r10 *)
bvAssign r10 (bvVar rdx);
(* shr    $0x33,%rdx *)
(* bvSplit rdx tmp (bvVar rdx) (fromNat 51); *)
(* NOTE: merge 'shr $0x33,%rdx' with 'and '%rsi,%r10' *)
bvConcatShl rdx r10 (bvConst (fromPosZ 0%Z)) (bvVar rdx) (fromNat 13);
(* imul   $0x13,%rdx,%rdx *)
bvMul rdx (bvConst (fromPosZ 19%Z)) (bvVar rdx);
(* add    %rdx,%rcx *)
bvAddC carry rcx (bvVar rdx) (bvVar rcx);
(* and    %rsi,%r10 *)
(* bvSplit tmp r10 (bvVar r10) (fromNat 51); *)
(* NOTE: see above *)
(* mov    %rcx,(%rdi)                              #! EA = L0x7fffffffdb40 *)
bvAssign L0x7fffffffdb40 (bvVar rcx);
(* mov    %r8,0x8(%rdi)                            #! EA = L0x7fffffffdb48 *)
bvAssign L0x7fffffffdb48 (bvVar r8);
(* mov    %r9,0x10(%rdi)                           #! EA = L0x7fffffffdb50 *)
bvAssign L0x7fffffffdb50 (bvVar r9);
(* mov    %rax,0x18(%rdi)                          #! EA = L0x7fffffffdb58 *)
bvAssign L0x7fffffffdb58 (bvVar rax);
(* mov    %r10,0x20(%rdi)                          #! EA = L0x7fffffffdb60 *)
bvAssign L0x7fffffffdb60 (bvVar r10);

bvAssign t0 (bvVar L0x7fffffffdb40);
bvAssign t1 (bvVar L0x7fffffffdb48);
bvAssign t2 (bvVar L0x7fffffffdb50);
bvAssign t3 (bvVar L0x7fffffffdb58);
bvAssign t4 (bvVar L0x7fffffffdb60)
].
