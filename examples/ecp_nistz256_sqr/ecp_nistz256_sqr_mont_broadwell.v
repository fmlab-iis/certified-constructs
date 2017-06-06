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
let L0x62c080 := 9 in
let L0x62c088 := 3 in
let L0x62c090 := 8 in
let L0x62c098 := 2 in

let L0x427008 := 14 in
let L0x427018 := 13 in

let rax := 17 in
let rbp := 11 in
let rcx := 16 in
let rdx := 10 in
let r8 := 7 in
let r9 := 12 in
let r10 := 5 in
let r11 := 6 in
let r12 := 0 in
let r13 := 4 in
let r14 := 1 in
let r15 := 15 in

let rsi := 200  in
let eax := 201  in
let tmp := 997  in
let overflow := 998  in
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

(* mov    (%rsi),%rdx                              #! EA = L0x62c080 *)
bvAssign (rdx) (bvVar (L0x62c080));
(* mov    0x8(%rsi),%r14                           #! EA = L0x62c088 *)
bvAssign (r14) (bvVar (L0x62c088));
(* mov    0x10(%rsi),%r15                          #! EA = L0x62c090 *)
bvAssign (r15) (bvVar (L0x62c090));
(* mov    0x18(%rsi),%r8                           #! EA = L0x62c098 *)
bvAssign (r8) (bvVar (L0x62c098));
(* mulx   %r14,%r9,%r10 *)
bvMulf (r10) (r9) (bvVar (r14)) (bvVar rdx);
(* mulx   %r15,%rcx,%r11 *)
bvMulf (r11) (rcx) (bvVar (r15)) (bvVar rdx);
(* xor    %eax,%eax *)
bvAssign (eax) (bvConst (fromPosZ 0%Z));
bvAssign (carry) (bvConst (fromPosZ 0%Z));
bvAssign (overflow) (bvConst (fromPosZ 0%Z));
(* adc    %rcx,%r10 *)
bvAdcC carry (r10) (bvVar (rcx)) (bvVar (r10)) (carry);
(* mulx   %r8,%rbp,%r12 *)
bvMulf (r12) (rbp) (bvVar (r8)) (bvVar rdx);
(* mov    %r14,%rdx *)
bvAssign (rdx) (bvVar (r14));
(* adc    %rbp,%r11 *)
bvAdcC carry (r11) (bvVar (rbp)) (bvVar (r11)) (carry);
(* adc    $0x0,%r12 *)
bvAdc (r12) (bvVar (r12)) (bvConst (fromPosZ 0%Z)) (carry);
(* xor    %r13,%r13 *)
bvAssign (r13) (bvConst (fromPosZ 0%Z));
bvAssign (carry) (bvConst (fromPosZ 0%Z));
bvAssign (overflow) (bvConst (fromPosZ 0%Z));

(* mulx   %r15,%rcx,%rbp *)
bvMulf (rbp) (rcx) (bvVar (r15)) (bvVar rdx);
(* adcx   %rcx,%r11 *)
bvAdcC carry (r11) (bvVar (rcx)) (bvVar (r11)) (carry);
(* adox   %rbp,%r12 *)
bvAdcC overflow (r12) (bvVar (rbp)) (bvVar (r12)) (overflow);
(* mulx   %r8,%rcx,%rbp *)
bvMulf (rbp) (rcx) (bvVar (r8)) (bvVar rdx);
(* mov    %r15,%rdx *)
bvAssign (rdx) (bvVar (r15));
(* adcx   %rcx,%r12 *)
bvAdcC carry (r12) (bvVar (rcx)) (bvVar (r12)) (carry);
(* adox   %rbp,%r13 *)
(* bvAdcC overflow (r13) (bvVar (rbp)) (bvVar (r13)) (overflow); *)
(* NOTE: ignore overflow because it is zero *)
bvAdc (r13) (bvVar (rbp)) (bvVar (r13)) (overflow);
(* adc    $0x0,%r13 *)
bvAdc (r13) (bvVar (r13)) (bvConst (fromPosZ 0%Z)) (carry);

(* mulx   %r8,%rcx,%r14 *)
bvMulf (r14) (rcx) (bvVar (r8)) (bvVar rdx);
(* mov    0x80(%rsi),%rdx                          #! EA = L0x62c080 *)
bvAssign (rdx) (bvVar (L0x62c080));
(* xor    %r15,%r15 *)
bvAssign (r15) (bvConst (fromPosZ 0%Z));
bvAssign (carry) (bvConst (fromPosZ 0%Z));
bvAssign (overflow) (bvConst (fromPosZ 0%Z));
(* adcx   %r9,%r9 *)
bvAdcC carry (r9) (bvVar (r9)) (bvVar (r9)) (carry);
(* adox   %rcx,%r13 *)
bvAdcC overflow (r13) (bvVar (rcx)) (bvVar (r13)) (overflow);
(* adcx   %r10,%r10 *)
bvAdcC carry (r10) (bvVar (r10)) (bvVar (r10)) (carry);
(* adox   %r15,%r14 *)
(* bvAdcC overflow (r14) (bvVar (r15)) (bvVar (r14)) (overflow); *)
(* NOTE: ignore overflow because it is zero *)
bvAdc (r14) (bvVar (r15)) (bvVar (r14)) (overflow);
(* NOTE: clear overflow since it is zero *)
bvAssign overflow (bvConst (fromPosZ 0%Z));

(* mulx   %rdx,%r8,%rbp *)
bvMulf (rbp) (r8) (bvVar (rdx)) (bvVar rdx);
(* mov    0x88(%rsi),%rdx                          #! EA = L0x62c088 *)
bvAssign (rdx) (bvVar (L0x62c088));
(* adcx   %r11,%r11 *)
bvAdcC carry (r11) (bvVar (r11)) (bvVar (r11)) (carry);
(* adox   %rbp,%r9 *)
bvAdcC overflow (r9) (bvVar (rbp)) (bvVar (r9)) (overflow);
(* adcx   %r12,%r12 *)
bvAdcC carry (r12) (bvVar (r12)) (bvVar (r12)) (carry);
(* mulx   %rdx,%rcx,%rax *)
bvMulf (rax) (rcx) (bvVar (rdx)) (bvVar rdx);
(* mov    0x90(%rsi),%rdx                          #! EA = L0x62c090 *)
bvAssign (rdx) (bvVar (L0x62c090));
(* adcx   %r13,%r13 *)
bvAdcC carry (r13) (bvVar (r13)) (bvVar (r13)) (carry);
(* adox   %rcx,%r10 *)
bvAdcC overflow (r10) (bvVar (rcx)) (bvVar (r10)) (overflow);
(* adcx   %r14,%r14 *)
bvAdcC carry (r14) (bvVar (r14)) (bvVar (r14)) (carry);
(* addr32 mulx %rdx,%rcx,%rbp *)
bvMulf (rbp) (rcx) (bvVar (rdx)) (bvVar rdx);
(* mov    0x98(%rsi),%rdx                          #! EA = L0x62c098 *)
bvAssign (rdx) (bvVar (L0x62c098));
(* adox   %rax,%r11 *)
bvAdcC overflow (r11) (bvVar (rax)) (bvVar (r11)) (overflow);
(* adcx   %r15,%r15 *)
(* bvAdcC carry (r15) (bvVar (r15)) (bvVar (r15)) (carry); *)
(* NOTE: ignore carry because it is zero *)
bvAdc (r15) (bvVar (r15)) (bvVar (r15)) (carry);
(* adox   %rcx,%r12 *)
bvAdcC overflow (r12) (bvVar (rcx)) (bvVar (r12)) (overflow);
(* mov    $0x20,%rsi *)
bvAssign (rsi) (bvConst (fromPosZ 32%Z));
(* adox   %rbp,%r13 *)
bvAdcC overflow (r13) (bvVar (rbp)) (bvVar (r13)) (overflow);
(* addr32 addr32 mulx %rdx,%rcx,%rax *)
bvMulf (rax) (rcx) (bvVar (rdx)) (bvVar rdx);
(* mov    -0xccf(%rip),%rdx        # 0x427018      #! EA = L0x427018 *)
bvAssign (rdx) (bvVar (L0x427018));
(* adox   %rcx,%r14 *)
bvAdcC overflow (r14) (bvVar (rcx)) (bvVar (r14)) (overflow);
(* shlx   %rsi,%r8,%rcx *)
(* bvShl (rcx) (bvVar (r8)) (fromNat 32); *)
(* adox   %rax,%r15 *)
(* bvAdcC overflow (r15) (bvVar (rax)) (bvVar (r15)) (overflow); *)
(* NOTE: ignore overflow because it is zero *)
bvAdc (r15) (bvVar (rax)) (bvVar (r15)) (overflow);

(* reduction *)

(* shrx   %rsi,%r8,%rax *)
(* bvSplit (rax) tmp (bvVar (r8)) (fromNat 32); *)
(* NOTE: merge 'shlx %rsi,%r8,%rcx' and 'shrx %rsi,%r8,%rax' *)
bvSplit rax rcx (bvVar r8) (fromNat 32);
bvShl rcx (bvVar rcx) (fromNat 32);
(* mov    %rdx,%rbp *)
bvAssign (rbp) (bvVar (rdx));
(* add    %rcx,%r9 *)
bvAddC carry (r9) (bvVar (rcx)) (bvVar (r9));
(* adc    %rax,%r10 *)
bvAdcC carry (r10) (bvVar (rax)) (bvVar (r10)) (carry);

(* mulx   %r8,%rcx,%r8 *)
bvMulf (r8) (rcx) (bvVar (r8)) (bvVar rdx);
(* adc    %rcx,%r11 *)
bvAdcC carry (r11) (bvVar (rcx)) (bvVar (r11)) (carry);
(* shlx   %rsi,%r9,%rcx *)
(* bvShl (rcx) (bvVar (r9)) (fromNat 32); *)
(* adc    $0x0,%r8 *)
bvAdc (r8) (bvVar (r8)) (bvConst (fromPosZ 0%Z)) (carry);
(* shrx   %rsi,%r9,%rax *)
(* bvSplit (rax) tmp (bvVar (r9)) (fromNat 32); *)
(* NOTE: merge 'shlx %rsi,%r9,%rcx' and 'shrx %rsi,%r9,%rax' *)
bvSplit rax rcx (bvVar r9) (fromNat 32);
bvShl rcx (bvVar rcx) (fromNat 32);

(* add    %rcx,%r10 *)
bvAddC carry (r10) (bvVar (rcx)) (bvVar (r10));
(* adc    %rax,%r11 *)
bvAdcC carry (r11) (bvVar (rax)) (bvVar (r11)) (carry);

(* mulx   %r9,%rcx,%r9 *)
bvMulf (r9) (rcx) (bvVar (r9)) (bvVar rdx);
(* adc    %rcx,%r8 *)
bvAdcC carry (r8) (bvVar (rcx)) (bvVar (r8)) (carry);
(* shlx   %rsi,%r10,%rcx *)
(* bvShl (rcx) (bvVar (r10)) (fromNat 32); *)
(* adc    $0x0,%r9 *)
bvAdc (r9) (bvVar (r9)) (bvConst (fromPosZ 0%Z)) (carry);
(* shrx   %rsi,%r10,%rax *)
(* bvSplit (rax) tmp (bvVar (r10)) (fromNat 32); *)
(* NOTE: merge 'shlx %rsi,%r10,%rcx' and 'shrx %rsi,%r10,%rax' *)
bvSplit rax rcx (bvVar r10) (fromNat 32);
bvShl rcx (bvVar rcx) (fromNat 32);

(* add    %rcx,%r11 *)
bvAddC carry (r11) (bvVar (rcx)) (bvVar (r11));
(* adc    %rax,%r8 *)
bvAdcC carry (r8) (bvVar (rax)) (bvVar (r8)) (carry);

(* mulx   %r10,%rcx,%r10 *)
bvMulf (r10) (rcx) (bvVar (r10)) (bvVar rdx);
(* adc    %rcx,%r9 *)
bvAdcC carry (r9) (bvVar (rcx)) (bvVar (r9)) (carry);
(* shlx   %rsi,%r11,%rcx *)
(* bvShl (rcx) (bvVar (r11)) (fromNat 32); *)
(* adc    $0x0,%r10 *)
bvAdc (r10) (bvVar (r10)) (bvConst (fromPosZ 0%Z)) (carry);
(* shrx   %rsi,%r11,%rax *)
(* bvSplit (rax) tmp (bvVar (r11)) (fromNat 32); *)
(* NOTE: merge 'shlx %rsi,%r11,%rcx' and 'shrx %rsi,%r11,%rax' *)
bvSplit rax rcx (bvVar r11) (fromNat 32);
bvShl rcx (bvVar rcx) (fromNat 32);

(* add    %rcx,%r8 *)
bvAddC carry (r8) (bvVar (rcx)) (bvVar (r8));
(* adc    %rax,%r9 *)
bvAdcC carry (r9) (bvVar (rax)) (bvVar (r9)) (carry);

(* mulx   %r11,%rcx,%r11 *)
bvMulf (r11) (rcx) (bvVar (r11)) (bvVar rdx);
(* adc    %rcx,%r10 *)
bvAdcC carry (r10) (bvVar (rcx)) (bvVar (r10)) (carry);
(* adc    $0x0,%r11 *)
bvAdc (r11) (bvVar (r11)) (bvConst (fromPosZ 0%Z)) (carry);

(* xor    %rdx,%rdx *)
bvAssign (rdx) (bvConst (fromPosZ 0%Z));
bvAssign (carry) (bvConst (fromPosZ 0%Z));
bvAssign (overflow) (bvConst (fromPosZ 0%Z));
(* add    %r8,%r12 *)
bvAddC carry (r12) (bvVar (r8)) (bvVar (r12));
(* mov    -0xd6b(%rip),%rsi        # 0x427008      #! EA = L0x427008 *)
bvAssign (rsi) (bvVar (L0x427008));
(* adc    %r9,%r13 *)
bvAdcC carry (r13) (bvVar (r9)) (bvVar (r13)) (carry);
(* mov    %r12,%r8 *)
bvAssign (r8) (bvVar (r12));
(* adc    %r10,%r14 *)
bvAdcC carry (r14) (bvVar (r10)) (bvVar (r14)) (carry);
(* adc    %r11,%r15 *)
bvAdcC carry (r15) (bvVar (r11)) (bvVar (r15)) (carry);
(* mov    %r13,%r9 *)
bvAssign (r9) (bvVar (r13));
(* adc    $0x0,%rdx *)
bvAdc (rdx) (bvVar (rdx)) (bvConst (fromPosZ 0%Z)) (carry);

bvAssign t0 (bvVar r12);
bvAssign t1 (bvVar r13);
bvAssign t2 (bvVar r14);
bvAssign t3 (bvVar r15);
bvAssign t4 (bvVar rdx)

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
     (bvrvar a0) <r (bvposz (2^64)%Z);
     (bvrvar a1) <r (bvposz (2^64)%Z);
     (bvrvar a2) <r (bvposz (2^64)%Z);
     (bvrvar a3) <r (bvposz (2^64)%Z)
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
  let r8 := 7 in
  let r9 := 12 in
  let r10 := 5 in
  let r11 := 6 in
  let r12 := 0 in
  let r13 := 4 in
  let r14 := 1 in
  let r15 := 15 in
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
       (bvrvar t0) <r (bvposz (2^64)%Z);
       (bvrvar t1) <r (bvposz (2^64)%Z);
       (bvrvar t2) <r (bvposz (2^64)%Z);
       (bvrvar t3) <r (bvposz (2^64)%Z);
       (bvrvar t4) <r (bvposz (2^1)%Z)
    ]
      
.

Definition nistz256_sqr_mont_spec :=
  {| spre := nistz256_sqr_mont_pre;
     sprog := program;
     spost := nistz256_sqr_mont_post |}.

Lemma valid_nistz256_sqr_mont :
  valid_bvspec (nistz256_sqr_mont_inputs, nistz256_sqr_mont_spec).
Proof.
  time "valid_nistz256_sqr_mont" verify_bvspec .
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.
