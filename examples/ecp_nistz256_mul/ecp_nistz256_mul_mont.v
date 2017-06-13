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
let L0x62c080 := 8 in  (* ap *)
let L0x62c088 := 2 in
let L0x62c090 := 7 in
let L0x62c098 := 1 in

let L0x62c0a0 := 14 in (* bp *)
let L0x62c0a8 := 19 in
let L0x62c0b0 := 10 in
let L0x62c0b8 := 15 in

let L0x427008 := 13 in (* p *)
let L0x427018 := 12 in

let rax := 20 in
let rbp := 18 in
let rcx := 16 in
let rdx := 9 in
let r8 := 6 in
let r9 := 11 in
let r10 := 4 in
let r11 := 5 in
let r12 := 17 in
let r13 := 3 in
let r15 := 0 in

let   r14 := 100 in
let   rbx := 101 in
let   tmp := 998 in
let carry := 999 in

let a0 := 1000 in
let a1 := 1001 in
let a2 := 1002 in
let a3 := 1003 in
let b0 := 2000 in
let b1 := 2001 in
let b2 := 2002 in
let b3 := 2003 in
let t0 := 3000 in
let t1 := 3001 in
let t2 := 3002 in
let t3 := 3003 in
let t4 := 3004 in
let p0 := 18446744073709551615%Z in (* FFFFFFFFFFFFFFFF *)
let p1 := 4294967295%Z in           (* 00000000FFFFFFFF *)
let p2 := 0%Z in                    (* 0000000000000000 *)
let p3 := 18446744069414584321%Z in (* FFFFFFFF00000001 *)

[::

bvAssign L0x62c080 (bvVar a0);
bvAssign L0x62c088 (bvVar a1);
bvAssign L0x62c090 (bvVar a2);
bvAssign L0x62c098 (bvVar a3);

bvAssign L0x62c0a0 (bvVar b0);
bvAssign L0x62c0a8 (bvVar b1);
bvAssign L0x62c0b0 (bvVar b2);
bvAssign L0x62c0b8 (bvVar b3);

bvAssign L0x427008 (bvConst (fromPosZ p1));
bvAssign L0x427018 (bvConst (fromPosZ p3));

(* multiplication *)

(* mov    (%rdx),%rax                              #! EA = L0x62c0a0 *)
bvAssign (rax) (bvVar (L0x62c0a0));
(* mov    (%rsi),%r9                               #! EA = L0x62c080 *)
bvAssign (r9) (bvVar (L0x62c080));
(* mov    0x8(%rsi),%r10                           #! EA = L0x62c088 *)
bvAssign (r10) (bvVar (L0x62c088));
(* mov    0x10(%rsi),%r11                          #! EA = L0x62c090 *)
bvAssign (r11) (bvVar (L0x62c090));
(* mov    0x18(%rsi),%r12                          #! EA = L0x62c098 *)
bvAssign (r12) (bvVar (L0x62c098));
(* mov    %rax,%rbp *)
bvAssign (rbp) (bvVar (rax));
(* mul    %r9 *)
bvMulf rdx rax (bvVar (r9)) (bvVar rax);
(* mov    -0x525(%rip),%r14        # 0x427008      #! EA = L0x427008 *)
bvAssign (r14) (bvVar (L0x427008));
(* mov    %rax,%r8 *)
bvAssign (r8) (bvVar (rax));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* mov    %rdx,%r9 *)
bvAssign (r9) (bvVar (rdx));
(* mul    %r10 *)
bvMulf rdx rax (bvVar (r10)) (bvVar rax);
(* mov    -0x528(%rip),%r15        # 0x427018      #! EA = L0x427018 *)
bvAssign (r15) (bvVar (L0x427018));
(* add    %rax,%r9 *)
bvAddC carry (r9) (bvVar (rax)) (bvVar (r9));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%r10 *)
bvAssign (r10) (bvVar (rdx));
(* mul    %r11 *)
bvMulf rdx rax (bvVar (r11)) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry (r10) (bvVar (rax)) (bvVar (r10));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%r11 *)
bvAssign (r11) (bvVar (rdx));
(* mul    %r12 *)
bvMulf rdx rax (bvVar (r12)) (bvVar rax);
(* add    %rax,%r11 *)
bvAddC carry (r11) (bvVar (rax)) (bvVar (r11));
(* mov    %r8,%rax *)
bvAssign (rax) (bvVar (r8));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* xor    %r13,%r13 *)
bvAssign (r13) (bvConst (fromPosZ 0%Z));
(* mov    %rdx,%r12 *)
bvAssign (r12) (bvVar (rdx));
(* mov    %r8,%rbp *)
bvAssign (rbp) (bvVar (r8));
(* shl    $0x20,%r8 *)
(* bvShl (r8) (bvVar (r8)) (fromNat 32); *)
(* mul    %r15 *)
bvMulf rdx rax (bvVar (r15)) (bvVar rax);
(* shr    $0x20,%rbp *)
(* bvSplit (rbp) tmp (bvVar (rbp)) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r8' and 'shr $0x20,%rbp' *)
bvSplit rbp r8 (bvVar r8) (fromNat 32);
bvShl r8 (bvVar r8) (fromNat 32);
(* add    %r8,%r9 *)
bvAddC carry (r9) (bvVar (r8)) (bvVar (r9));
(* adc    %rbp,%r10 *)
bvAdcC carry (r10) (bvVar (rbp)) (bvVar (r10)) (carry);
(* adc    %rax,%r11 *)
bvAdcC carry (r11) (bvVar (rax)) (bvVar (r11)) (carry);
(* mov    0x8(%rbx),%rax                           #! EA = L0x62c0a8 *)
bvAssign (rax) (bvVar (L0x62c0a8));
(* adc    %rdx,%r12 *)
bvAdcC carry (r12) (bvVar (rdx)) (bvVar (r12)) (carry);
(* adc    $0x0,%r13 *)
bvAdc (r13) (bvVar (r13)) (bvConst (fromPosZ 0%Z)) (carry);
(* xor    %r8,%r8 *)
bvAssign (r8) (bvConst (fromPosZ 0%Z));
(* mov    %rax,%rbp *)
bvAssign (rbp) (bvVar (rax));
(* mulq   (%rsi)                                   #! EA = L0x62c080 *)
bvMulf rdx rax (bvVar (L0x62c080)) (bvVar rax);
(* add    %rax,%r9 *)
bvAddC carry (r9) (bvVar (rax)) (bvVar (r9));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mulq   0x8(%rsi)                                #! EA = L0x62c088 *)
bvMulf rdx rax (bvVar (L0x62c088)) (bvVar rax);
(* add    %rcx,%r10 *)
bvAddC carry (r10) (bvVar (rcx)) (bvVar (r10));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rax,%r10 *)
bvAddC carry (r10) (bvVar (rax)) (bvVar (r10));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mulq   0x10(%rsi)                               #! EA = L0x62c090 *)
bvMulf rdx rax (bvVar (L0x62c090)) (bvVar rax);
(* add    %rcx,%r11 *)
bvAddC carry (r11) (bvVar (rcx)) (bvVar (r11));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rax,%r11 *)
bvAddC carry (r11) (bvVar (rax)) (bvVar (r11));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mulq   0x18(%rsi)                               #! EA = L0x62c098 *)
bvMulf rdx rax (bvVar (L0x62c098)) (bvVar rax);
(* add    %rcx,%r12 *)
bvAddC carry (r12) (bvVar (rcx)) (bvVar (r12));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rax,%r12 *)
bvAddC carry (r12) (bvVar (rax)) (bvVar (r12));
(* mov    %r9,%rax *)
bvAssign (rax) (bvVar (r9));
(* adc    %rdx,%r13 *)
bvAdcC carry (r13) (bvVar (rdx)) (bvVar (r13)) (carry);
(* adc    $0x0,%r8 *)
bvAdc (r8) (bvVar (r8)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %r9,%rbp *)
bvAssign (rbp) (bvVar (r9));
(* shl    $0x20,%r9 *)
(* bvShl (r9) (bvVar (r9)) (fromNat 32); *)
(* mul    %r15 *)
bvMulf rdx rax (bvVar (r15)) (bvVar rax);
(* shr    $0x20,%rbp *)
(* bvSplit (rbp) tmp (bvVar (rbp)) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r9' and 'shr $0x20,%rbp' *)
bvSplit rbp r9 (bvVar r9) (fromNat 32);
bvShl r9 (bvVar r9) (fromNat 32);
(* add    %r9,%r10 *)
bvAddC carry (r10) (bvVar (r9)) (bvVar (r10));
(* adc    %rbp,%r11 *)
bvAdcC carry (r11) (bvVar (rbp)) (bvVar (r11)) (carry);
(* adc    %rax,%r12 *)
bvAdcC carry (r12) (bvVar (rax)) (bvVar (r12)) (carry);
(* mov    0x10(%rbx),%rax                          #! EA = L0x62c0b0 *)
bvAssign (rax) (bvVar (L0x62c0b0));
(* adc    %rdx,%r13 *)
bvAdcC carry (r13) (bvVar (rdx)) (bvVar (r13)) (carry);
(* adc    $0x0,%r8 *)
bvAdc (r8) (bvVar (r8)) (bvConst (fromPosZ 0%Z)) (carry);
(* xor    %r9,%r9 *)
bvAssign (r9) (bvConst (fromPosZ 0%Z));
(* mov    %rax,%rbp *)
bvAssign (rbp) (bvVar (rax));
(* mulq   (%rsi)                                   #! EA = L0x62c080 *)
bvMulf rdx rax (bvVar (L0x62c080)) (bvVar rax);
(* add    %rax,%r10 *)
bvAddC carry (r10) (bvVar (rax)) (bvVar (r10));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mulq   0x8(%rsi)                                #! EA = L0x62c088 *)
bvMulf rdx rax (bvVar (L0x62c088)) (bvVar rax);
(* add    %rcx,%r11 *)
bvAddC carry (r11) (bvVar (rcx)) (bvVar (r11));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rax,%r11 *)
bvAddC carry (r11) (bvVar (rax)) (bvVar (r11));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mulq   0x10(%rsi)                               #! EA = L0x62c090 *)
bvMulf rdx rax (bvVar (L0x62c090)) (bvVar rax);
(* add    %rcx,%r12 *)
bvAddC carry (r12) (bvVar (rcx)) (bvVar (r12));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rax,%r12 *)
bvAddC carry (r12) (bvVar (rax)) (bvVar (r12));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mulq   0x18(%rsi)                               #! EA = L0x62c098 *)
bvMulf rdx rax (bvVar (L0x62c098)) (bvVar rax);
(* add    %rcx,%r13 *)
bvAddC carry (r13) (bvVar (rcx)) (bvVar (r13));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rax,%r13 *)
bvAddC carry (r13) (bvVar (rax)) (bvVar (r13));
(* mov    %r10,%rax *)
bvAssign (rax) (bvVar (r10));
(* adc    %rdx,%r8 *)
bvAdcC carry (r8) (bvVar (rdx)) (bvVar (r8)) (carry);
(* adc    $0x0,%r9 *)
bvAdc (r9) (bvVar (r9)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %r10,%rbp *)
bvAssign (rbp) (bvVar (r10));
(* shl    $0x20,%r10 *)
(* bvShl (r10) (bvVar (r10)) (fromNat 32); *)
(* mul    %r15 *)
bvMulf rdx rax (bvVar (r15)) (bvVar rax);
(* shr    $0x20,%rbp *)
(* bvSplit (rbp) tmp (bvVar (rbp)) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r10' and 'shr $0x20,%rbp' *)
bvSplit rbp r10 (bvVar r10) (fromNat 32);
bvShl r10 (bvVar r10) (fromNat 32);
(* add    %r10,%r11 *)
bvAddC carry (r11) (bvVar (r10)) (bvVar (r11));
(* adc    %rbp,%r12 *)
bvAdcC carry (r12) (bvVar (rbp)) (bvVar (r12)) (carry);
(* adc    %rax,%r13 *)
bvAdcC carry (r13) (bvVar (rax)) (bvVar (r13)) (carry);
(* mov    0x18(%rbx),%rax                          #! EA = L0x62c0b8 *)
bvAssign (rax) (bvVar (L0x62c0b8));
(* adc    %rdx,%r8 *)
bvAdcC carry (r8) (bvVar (rdx)) (bvVar (r8)) (carry);
(* adc    $0x0,%r9 *)
bvAdc (r9) (bvVar (r9)) (bvConst (fromPosZ 0%Z)) (carry);
(* xor    %r10,%r10 *)
bvAssign (r10) (bvConst (fromPosZ 0%Z));
(* mov    %rax,%rbp *)
bvAssign (rbp) (bvVar (rax));
(* mulq   (%rsi)                                   #! EA = L0x62c080 *)
bvMulf rdx rax (bvVar (L0x62c080)) (bvVar rax);
(* add    %rax,%r11 *)
bvAddC carry (r11) (bvVar (rax)) (bvVar (r11));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mulq   0x8(%rsi)                                #! EA = L0x62c088 *)
bvMulf rdx rax (bvVar (L0x62c088)) (bvVar rax);
(* add    %rcx,%r12 *)
bvAddC carry (r12) (bvVar (rcx)) (bvVar (r12));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rax,%r12 *)
bvAddC carry (r12) (bvVar (rax)) (bvVar (r12));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mulq   0x10(%rsi)                               #! EA = L0x62c090 *)
bvMulf rdx rax (bvVar (L0x62c090)) (bvVar rax);
(* add    %rcx,%r13 *)
bvAddC carry (r13) (bvVar (rcx)) (bvVar (r13));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rax,%r13 *)
bvAddC carry (r13) (bvVar (rax)) (bvVar (r13));
(* mov    %rbp,%rax *)
bvAssign (rax) (bvVar (rbp));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %rdx,%rcx *)
bvAssign (rcx) (bvVar (rdx));
(* mulq   0x18(%rsi)                               #! EA = L0x62c098 *)
bvMulf rdx rax (bvVar (L0x62c098)) (bvVar rax);
(* add    %rcx,%r8 *)
bvAddC carry (r8) (bvVar (rcx)) (bvVar (r8));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rax,%r8 *)
bvAddC carry (r8) (bvVar (rax)) (bvVar (r8));
(* mov    %r11,%rax *)
bvAssign (rax) (bvVar (r11));
(* adc    %rdx,%r9 *)
bvAdcC carry (r9) (bvVar (rdx)) (bvVar (r9)) (carry);
(* adc    $0x0,%r10 *)
bvAdc (r10) (bvVar (r10)) (bvConst (fromPosZ 0%Z)) (carry);
(* mov    %r11,%rbp *)
bvAssign (rbp) (bvVar (r11));
(* shl    $0x20,%r11 *)
(* bvShl (r11) (bvVar (r11)) (fromNat 32); *)
(* mul    %r15 *)
bvMulf rdx rax (bvVar (r15)) (bvVar rax);
(* shr    $0x20,%rbp *)
(* bvSplit (rbp) tmp (bvVar (rbp)) (fromNat 32); *)
(* NOTE: merge 'shl $0x20,%r11' and 'shr $0x20,%rbp' *)
bvSplit rbp r11 (bvVar r11) (fromNat 32);
bvShl r11 (bvVar r11) (fromNat 32);
(* add    %r11,%r12 *)
bvAddC carry (r12) (bvVar (r11)) (bvVar (r12));
(* adc    %rbp,%r13 *)
bvAdcC carry (r13) (bvVar (rbp)) (bvVar (r13)) (carry);
(* mov    %r12,%rcx *)
bvAssign (rcx) (bvVar (r12));
(* adc    %rax,%r8 *)
bvAdcC carry (r8) (bvVar (rax)) (bvVar (r8)) (carry);
(* adc    %rdx,%r9 *)
bvAdcC carry (r9) (bvVar (rdx)) (bvVar (r9)) (carry);
(* mov    %r13,%rbp *)
bvAssign (rbp) (bvVar (r13));
(* adc    $0x0,%r10 *)
bvAdc (r10) (bvVar (r10)) (bvConst (fromPosZ 0%Z)) (carry);

bvAssign t0 (bvVar r12);
bvAssign t1 (bvVar r13);
bvAssign t2 (bvVar r8);
bvAssign t3 (bvVar r9);
bvAssign t4 (bvVar r10)

].


Definition radix64 := @limbs 64 .

Definition nistz256_mul_mont_inputs : VS.t :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  b0 := 2000 in
  let  b1 := 2001 in
  let  b2 := 2002 in
  let  b3 := 2003 in
  let  t0 := 3000 in
  let  t1 := 3001 in
  let  t2 := 3002 in
  let  t3 := 3003 in
  let  t4 := 3004 in
  VSLemmas.OP.P.of_list [:: a0; a1; a2; a3; b0; b1; b2; b3 ].

Definition nistz256_mul_mont_pre : bexp := 
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  b0 := 2000 in
  let  b1 := 2001 in
  let  b2 := 2002 in
  let  b3 := 2003 in
bvrands
  [::
     (bvrvar a0) <=r (bvposz (2^64)%Z);
     (bvrvar a1) <=r (bvposz (2^64)%Z);
     (bvrvar a2) <=r (bvposz (2^64)%Z);
     (bvrvar a3) <=r (bvposz (2^64)%Z);
     (bvrvar b0) <=r (bvposz (2^64)%Z);
     (bvrvar b1) <=r (bvposz (2^64)%Z);
     (bvrvar b2) <=r (bvposz (2^64)%Z);
     (bvrvar b3) <=r (bvposz (2^64)%Z)
  ].

Definition nistz256_mul_mont_post : bexp :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  let  b0 := 2000 in
  let  b1 := 2001 in
  let  b2 := 2002 in
  let  b3 := 2003 in
  let  t0 := 3000 in
  let  t1 := 3001 in
  let  t2 := 3002 in
  let  t3 := 3003 in
  let  t4 := 3004 in
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
         (radix64 [::bvevar b0; bvevar b1; bvevar b2; bvevar b3])
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
       (bvrvar t0) <r (bvposz (2^64)%Z);
       (bvrvar t1) <r (bvposz (2^64)%Z);
       (bvrvar t2) <r (bvposz (2^64)%Z);
       (bvrvar t3) <r (bvposz (2^64)%Z);
       (bvrvar t4) <r (bvposz (2^1)%Z)
    ]
      
.

Definition nistz256_mul_mont_spec :=
  {| spre := nistz256_mul_mont_pre;
     sprog := program;
     spost := nistz256_mul_mont_post |}.

Lemma valid_nistz256_mul_mont :
  valid_bvspec (nistz256_mul_mont_inputs, nistz256_mul_mont_spec).
Proof.
  time "valid_nistz256_mul_mont" verify_bvspec .
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.
