From Coq Require Import ZArith .
From mathcomp Require Import ssreflect ssrbool ssrnat seq .
From Common Require Import Bits .
From mQhasm Require Import bvDSL bvVerify Options .
Set Implicit Arguments .
Unset Strict Implicit .
Import Prenex Implicits .
Open Scope N_scope.
Open Scope bvdsl_scope.
Definition program :=
let L0x62c080 := 8 in
let L0x62c088 := 2 in
let L0x62c090 := 7 in
let L0x62c098 := 1 in
let L0x427008 := 13 in
let L0x427018 := 12 in
let r8 := 6 in
let r9 := 11 in
let r10 := 4 in
let r11 := 5 in
let r12 := 16 in
let r13 := 3 in
let r14 := 0 in
let r15 := 14 in
let rax := 17 in
let rbp := 10 in
let rcx := 15 in
let rdx := 9 in

let rsi := 100  in
let tmp := 998  in
let carry := 999  in
let  a0 := 1000 in
let  a1 := 1001 in
let  a2 := 1002 in
let  a3 := 1003 in
let  t0 := 5000 in
let  t1 := 5001 in
let  t2 := 5002 in
let  t3 := 5003 in
let  t4 := 5004 in
let  p0 := 18446744073709551615%Z in (* FFFFFFFFFFFFFFFF *)
let  p1 := 4294967295%Z in           (* 00000000FFFFFFFF *)
let  p2 := 0%Z in                    (* 0000000000000000 *)
let  p3 := 18446744069414584321%Z in (* FFFFFFFF00000001 *)
[::

bvAssign L0x62c080 (bvVar a0);
bvAssign L0x62c088 (bvVar a1);
bvAssign L0x62c090 (bvVar a2);
bvAssign L0x62c098 (bvVar a3);
bvAssign L0x427008 (bvConst (fromPosZ p1));
bvAssign L0x427018 (bvConst (fromPosZ p3));

(* multiplication *)

(* mov    (%rsi),%rax                              #! %ea = %L0x62c080 *)
bvAssign (rax) (bvVar (L0x62c080));
(* mov    0x8(%rsi),%r14                           #! %ea = %L0x62c088 *)
bvAssign (r14) (bvVar (L0x62c088));
(* mov    0x10(%rsi),%r15                          #! %ea = %L0x62c090 *)
bvAssign (r15) (bvVar (L0x62c090));
(* mov    0x18(%rsi),%r8                           #! %ea = %L0x62c098 *)
bvAssign (r8) (bvVar (L0x62c098));
(* #callq  0x4277e0 <__ecp_nistz256_sqr_montq> *)
(* mov    %rax,%r13 *)
bvAssign (r13) (bvVar (rax));
(* mul    %r14 *)
bvMulf rdx rax (bvVar (r14)) (bvVar rax);
(* mov    %rax,%r9 *)
bvAssign (r9) (bvVar (rax));
(* mov    %r15,%rax *)
bvAssign (rax) (bvVar (r15));
(* mov    %rdx,%r10 *)
bvAssign (r10) (bvVar (rdx));
(* mul    %r13 *)
bvMulf rdx rax (bvVar (r13)) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry (r10) (bvVar (rax)) (bvVar (r10));
(* mov    %r8,%rax *)
bvAssign (rax) (bvVar (r8));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%r11 *)
bvAssign (r11) (bvVar (rdx));
(* mul    %r13 *)
bvMulf rdx rax (bvVar (r13)) (bvVar rax);
(* add    %rax,%r11 *)
bvAddC carry (r11) (bvVar (rax)) (bvVar (r11));
(* mov    %r15,%rax *)
bvAssign (rax) (bvVar (r15));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%r12 *)
bvAssign (r12) (bvVar (rdx));
(* mul    %r14 *)
bvMulf rdx rax (bvVar (r14)) (bvVar rax);
(* add    %rax,%r11 *)
bvAddC carry (r11) (bvVar (rax)) (bvVar (r11));
(* mov    %r8,%rax *)
bvAssign (rax) (bvVar (r8));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rbp *)
bvAssign (rbp) (bvVar (rdx));
(* mul    %r14 *)
bvMulf rdx rax (bvVar (r14)) (bvVar rax);
(* add    %rax,%r12 *)
bvAddC carry (r12) (bvVar (rax)) (bvVar (r12));
(* mov    %r8,%rax *)
bvAssign (rax) (bvVar (r8));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rbp,%r12 *)
bvAddC carry (r12) (bvVar (rbp)) (bvVar (r12));
(* mov    %rdx,%r13 *)
bvAssign (r13) (bvVar (rdx));
(* adc    $0x0,%r13 *)
bvAdc (r13) (bvVar (r13)) (bvConst (fromPosZ 0%Z)) (carry);
(* mul    %r15 *)
bvMulf rdx rax (bvVar (r15)) (bvVar rax);
(* xor    %r15,%r15 *)
bvAssign (r15) (bvConst (fromPosZ 0%Z));
(* add    %rax,%r13 *)
bvAddC carry (r13) (bvVar (rax)) (bvVar (r13));
(* mov    (%rsi),%rax                              #! %ea = %L0x62c080 *)
bvAssign (rax) (bvVar (L0x62c080));
(* mov    %rdx,%r14 *)
bvAssign (r14) (bvVar (rdx));
(* adc    $0x0,%r14 *)
bvAdc (r14) (bvVar (r14)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %r9,%r9 *)
bvAddC carry (r9) (bvVar (r9)) (bvVar (r9));
(* adc    %r10,%r10 *)
bvAdcC carry (r10) (bvVar (r10)) (bvVar (r10)) (carry);
(* adc    %r11,%r11 *)
bvAdcC carry (r11) (bvVar (r11)) (bvVar (r11)) (carry);
(* adc    %r12,%r12 *)
bvAdcC carry (r12) (bvVar (r12)) (bvVar (r12)) (carry);
(* adc    %r13,%r13 *)
bvAdcC carry (r13) (bvVar (r13)) (bvVar (r13)) (carry);
(* adc    %r14,%r14 *)
bvAdcC carry (r14) (bvVar (r14)) (bvVar (r14)) (carry);
(* adc    $0x0,%r15 *)
bvAdc (r15) (bvVar (r15)) (bvConst (fromPosZ 0%Z)) (carry);
(* mul    %rax *)
bvMulf rdx rax (bvVar (rax)) (bvVar rax);
(* mov    %rax,%r8 *)
bvAssign (r8) (bvVar (rax));
(* mov    0x8(%rsi),%rax                           #! %ea = %L0x62c088 *)
bvAssign (rax) (bvVar (L0x62c088));
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mul    %rax *)
bvMulf rdx rax (bvVar (rax)) (bvVar rax);
(* add    %rcx,%r9 *)
bvAddC carry (r9) (bvVar (rcx)) (bvVar (r9));
(* adc    %rax,%r10 *)
bvAdcC carry (r10) (bvVar (rax)) (bvVar (r10)) (carry);
(* mov    0x10(%rsi),%rax                          #! %ea = %L0x62c090 *)
bvAssign (rax) (bvVar (L0x62c090));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mul    %rax *)
bvMulf rdx rax (bvVar (rax)) (bvVar rax);
(* add    %rcx,%r11 *)
bvAddC carry (r11) (bvVar (rcx)) (bvVar (r11));
(* adc    %rax,%r12 *)
bvAdcC carry (r12) (bvVar (rax)) (bvVar (r12)) (carry);
(* mov    0x18(%rsi),%rax                          #! %ea = %L0x62c098 *)
bvAssign (rax) (bvVar (L0x62c098));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mul    %rax *)
bvMulf rdx rax (bvVar (rax)) (bvVar rax);
(* add    %rcx,%r13 *)
bvAddC carry (r13) (bvVar (rcx)) (bvVar (r13));
(* adc    %rax,%r14 *)
bvAdcC carry (r14) (bvVar (rax)) (bvVar (r14)) (carry);
(* mov    %r8,%rax *)
bvAssign (rax) (bvVar (r8));
(* adc    %rdx,%r15 *)
(* bvAdcC carry (r15) (bvVar (rdx)) (bvVar (r15)) (carry); *)
(* NOTE: ignore carry because it should be zero *)
bvAdc (r15) (bvVar (rdx)) (bvVar (r15)) (carry);

(* reduction *)

(* mov    -0x8a2(%rip),%rsi        # 0x427008      #! %ea = %L0x427008 *)
bvAssign (rsi) (bvVar (L0x427008));
(* mov    -0x899(%rip),%rbp        # 0x427018      #! %ea = %L0x427018 *)
bvAssign (rbp) (bvVar (L0x427018));
(* mov    %r8,%rcx *)
bvAssign (rcx) (bvVar (r8));
(* shl    $0x20,%r8 *)
(* bvShl (r8) (bvVar (r8)) (fromNat 32); *)
(* mul    %rbp *)
bvMulf rdx rax (bvVar (rbp)) (bvVar rax);
(* shr    $0x20,%rcx *)
(* bvSplit (rcx) tmp (bvVar (rcx)) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r8' and 'shr $0x20,%rcs' *)
bvSplit rcx r8 (bvVar r8) (fromNat 32);
bvShl r8 (bvVar r8) (fromNat 32);
(* add    %r8,%r9 *)
bvAddC carry (r9) (bvVar (r8)) (bvVar (r9));
(* adc    %rcx,%r10 *)
bvAdcC carry (r10) (bvVar (rcx)) (bvVar (r10)) (carry);
(* adc    %rax,%r11 *)
bvAdcC carry (r11) (bvVar (rax)) (bvVar (r11)) (carry);
(* mov    %r9,%rax *)
bvAssign (rax) (bvVar (r9));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);

(* mov    %r9,%rcx *)
bvAssign (rcx) (bvVar (r9));
(* shl    $0x20,%r9 *)
(* bvShl (r9) (bvVar (r9)) (fromNat 32); *)
(* mov    %rdx,%r8 *)
bvAssign (r8) (bvVar (rdx));
(* mul    %rbp *)
bvMulf rdx rax (bvVar (rbp)) (bvVar rax);
(* shr    $0x20,%rcx *)
(* bvSplit (rcx) tmp (bvVar (rcx)) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r9' and 'shr $0x20,%rcs' *)
bvSplit rcx r9 (bvVar r9) (fromNat 32);
bvShl r9 (bvVar r9) (fromNat 32);
(* add    %r9,%r10 *)
bvAddC carry (r10) (bvVar (r9)) (bvVar (r10));
(* adc    %rcx,%r11 *)
bvAdcC carry (r11) (bvVar (rcx)) (bvVar (r11)) (carry);
(* adc    %rax,%r8 *)
bvAdcC carry (r8) (bvVar (rax)) (bvVar (r8)) (carry);
(* mov    %r10,%rax *)
bvAssign (rax) (bvVar (r10));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);

(* mov    %r10,%rcx *)
bvAssign (rcx) (bvVar (r10));
(* shl    $0x20,%r10 *)
(* bvShl (r10) (bvVar (r10)) (fromNat 32); *)
(* mov    %rdx,%r9 *)
bvAssign (r9) (bvVar (rdx));
(* mul    %rbp *)
bvMulf rdx rax (bvVar (rbp)) (bvVar rax);
(* shr    $0x20,%rcx *)
(* bvSplit (rcx) tmp (bvVar (rcx)) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r10' and 'shr $0x20,%rcs' *)
bvSplit rcx r10 (bvVar r10) (fromNat 32);
bvShl r10 (bvVar r10) (fromNat 32);
(* add    %r10,%r11 *)
bvAddC carry (r11) (bvVar (r10)) (bvVar (r11));
(* adc    %rcx,%r8 *)
bvAdcC carry (r8) (bvVar (rcx)) (bvVar (r8)) (carry);
(* adc    %rax,%r9 *)
bvAdcC carry (r9) (bvVar (rax)) (bvVar (r9)) (carry);
(* mov    %r11,%rax *)
bvAssign (rax) (bvVar (r11));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);

(* mov    %r11,%rcx *)
bvAssign (rcx) (bvVar (r11));
(* shl    $0x20,%r11 *)
(* bvShl (r11) (bvVar (r11)) (fromNat 32); *)
(* mov    %rdx,%r10 *)
bvAssign (r10) (bvVar (rdx));
(* mul    %rbp *)
bvMulf rdx rax (bvVar (rbp)) (bvVar rax);
(* shr    $0x20,%rcx *)
(* bvSplit (rcx) tmp (bvVar (rcx)) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r11' and 'shr $0x20,%rcs' *)
bvSplit rcx r11 (bvVar r11) (fromNat 32);
bvShl r11 (bvVar r11) (fromNat 32);
(* add    %r11,%r8 *)
bvAddC carry (r8) (bvVar (r11)) (bvVar (r8));
(* adc    %rcx,%r9 *)
bvAdcC carry (r9) (bvVar (rcx)) (bvVar (r9)) (carry);
(* adc    %rax,%r10 *)
bvAdcC carry (r10) (bvVar (rax)) (bvVar (r10)) (carry);
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);

(* xor    %r11,%r11 *)
bvAssign (r11) (bvConst (fromPosZ 0%Z));
(* add    %r8,%r12 *)
bvAddC carry (r12) (bvVar (r8)) (bvVar (r12));
(* adc    %r9,%r13 *)
bvAdcC carry (r13) (bvVar (r9)) (bvVar (r13)) (carry);
(* mov    %r12,%r8 *)
bvAssign (r8) (bvVar (r12));
(* adc    %r10,%r14 *)
bvAdcC carry (r14) (bvVar (r10)) (bvVar (r14)) (carry);
(* adc    %rdx,%r15 *)
bvAdcC carry (r15) (bvVar (rdx)) (bvVar (r15)) (carry);
(* mov    %r13,%r9 *)
bvAssign (r9) (bvVar (r13));
(* adc    $0x0,%r11 *)
bvAdc (r11) (bvVar (r11)) (bvConst (fromPosZ 0%Z)) (carry);

bvAssign t0  (bvVar (r12));
bvAssign t1  (bvVar (r13));
bvAssign t2  (bvVar (r14));
bvAssign t3  (bvVar (r15));
bvAssign t4  (bvVar (r11))

].

Definition radix64 := @limbs 64 .

Definition nistz256_sqr_mont_inputs : VS.t :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  t0 := 5000 in
  let  t1 := 5001 in
  let  t2 := 5002 in
  let  t3 := 5003 in
  let  t4 := 5004 in
  VSLemmas.OP.P.of_list [:: a0; a1; a2; a3 ].

Definition nistz256_sqr_mont_pre : bexp := 
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
bvrands
  [::
     (bvrvar a0) <=r (bvposz (2^64)%Z);
     (bvrvar a1) <=r (bvposz (2^64)%Z);
     (bvrvar a2) <=r (bvposz (2^64)%Z);
     (bvrvar a3) <=r (bvposz (2^64)%Z)
  ].

Definition nistz256_sqr_mont_post : bexp :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  t0 := 5000 in
  let  t1 := 5001 in
  let  t2 := 5002 in
  let  t3 := 5003 in
  let  t4 := 5004 in
  let  p0 := 18446744073709551615%Z in (* FFFFFFFFFFFFFFFF *)
  let  p1 := 4294967295%Z in           (* 00000000FFFFFFFF *)
  let  p2 := 0%Z in                    (* 0000000000000000 *)
  let  p3 := 18446744069414584321%Z in (* FFFFFFFF00000001 *)
  bvands2
    [::
       bveEqMod
       (
         (radix64 [::bvevar a0; bvevar a1; bvevar a2; bvevar a3])
         *e
         (radix64 [::bvevar a0; bvevar a1; bvevar a2; bvevar a3])
       )

       (
         (radix64 [::bvconst 0; bvconst 0; bvconst 0; bvconst 0;
                     bvevar t0; bvevar t1; bvevar t2; bvevar t3;
                     bvevar t4])
       )    

       (
         (radix64 [::bvconst p0; bvconst p1; bvconst p2; bvconst p3])
       )
    ]
    [::
       (bvrvar t0) <=r (bvposz (2^64)%Z);
       (bvrvar t1) <=r (bvposz (2^64)%Z);
       (bvrvar t2) <=r (bvposz (2^64)%Z);
       (bvrvar t3) <=r (bvposz (2^64)%Z);
       (bvrvar t4) <=r (bvposz (2^1)%Z)
    ]
      
.

Definition nistz256_sqr_mont_spec :=
  {| spre := nistz256_sqr_mont_pre;
     sprog := program;
     spost := nistz256_sqr_mont_post |}.

Lemma valid_nistz256_sqr_mont :
  valid_bvspec (nistz256_sqr_mont_inputs, nistz256_sqr_mont_spec).
Proof.
  time "valid_nistz256_sqr_mont" verify_bvspec with [:: With KeepUnused ] .
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.
