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

let L0x62c080 := 9 in  (* ap *)
let L0x62c088 := 3 in
let L0x62c090 := 8 in
let L0x62c098 := 2 in

let L0x62c0a0 := 15 in (* bp *)
let L0x62c0a8 := 19 in
let L0x62c0b0 := 11 in
let L0x62c0b8 := 16 in

let L0x427008 := 14 in (* p *)
let L0x427018 := 13 in 

let r8 := 7 in
let r9 := 10 in
let r10 := 5 in
let r11 := 6 in
let r12 := 0 in
let r13 := 4 in
let r15 := 1 in
let rbp := 18 in
let rcx := 17 in
let rdx := 12 in

let eax := 100 in
let r14 := 101 in
let rbx := 102 in
let tmp := 997 in
let overflow := 998 in
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
   
(* mov    (%rdx),%rdx                              #! EA = L0x62c0a0 *)
bvAssign (rdx) (bvVar (L0x62c0a0));
(* mov    (%rsi),%r9                               #! EA = L0x62c080 *)
bvAssign (r9) (bvVar (L0x62c080));
(* mov    0x8(%rsi),%r10                           #! EA = L0x62c088 *)
bvAssign (r10) (bvVar (L0x62c088));
(* mov    0x10(%rsi),%r11                          #! EA = L0x62c090 *)
bvAssign (r11) (bvVar (L0x62c090));
(* mov    0x18(%rsi),%r12                          #! EA = L0x62c098 *)
bvAssign (r12) (bvVar (L0x62c098));
(* mulx   %r9,%r8,%r9 *)
bvMulf (r9) (r8) (bvVar (r9)) (bvVar rdx);
(* mulx   %r10,%rcx,%r10 *)
bvMulf (r10) (rcx) (bvVar (r10)) (bvVar rdx);
(* mov    $0x20,%r14 *)
bvAssign (r14) (bvConst (fromPosZ 32%Z));
(* xor    %r13,%r13 *)
bvAssign (r13) (bvConst (fromPosZ 0%Z));
bvAssign (carry) (bvConst (fromPosZ 0%Z));
bvAssign (overflow) (bvConst (fromPosZ 0%Z));
(* mulx   %r11,%rbp,%r11 *)
bvMulf (r11) (rbp) (bvVar (r11)) (bvVar rdx);
(* mov    -0x9a8(%rip),%r15        # 0x427018      #! EA = L0x427018 *)
bvAssign (r15) (bvVar (L0x427018));
(* adc    %rcx,%r9 *)
bvAdcC carry (r9) (bvVar (rcx)) (bvVar (r9)) (carry);
(* mulx   %r12,%rcx,%r12 *)
bvMulf (r12) (rcx) (bvVar (r12)) (bvVar rdx);
(* mov    %r8,%rdx *)
bvAssign (rdx) (bvVar (r8));
(* adc    %rbp,%r10 *)
bvAdcC carry (r10) (bvVar (rbp)) (bvVar (r10)) (carry);
(* shlx   %r14,%r8,%rbp *)
(* bvShl (rbp) (bvVar (r8)) (fromNat 32); *)
(* adc    %rcx,%r11 *)
bvAdcC carry (r11) (bvVar (rcx)) (bvVar (r11)) (carry);
(* shrx   %r14,%r8,%rcx *)
(* bvSplit (rcx) tmp (bvVar (r8)) (fromNat 32); *)
(* NOTE: merge 'shlx %r14,%r8,%rbp' with shrx %r14,%r8,%rcx' *)
bvSplit rcx rbp (bvVar r8) (fromNat 32);
bvShl rbp (bvVar rbp) (fromNat 32);
(* adc    $0x0,%r12 *)
bvAdc (r12) (bvVar (r12)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rbp,%r9 *)
bvAddC carry (r9) (bvVar (rbp)) (bvVar (r9));
(* adc    %rcx,%r10 *)
bvAdcC carry (r10) (bvVar (rcx)) (bvVar (r10)) (carry);
(* mulx   %r15,%rcx,%rbp *)
bvMulf (rbp) (rcx) (bvVar (r15)) (bvVar rdx);
(* mov    0x8(%rbx),%rdx                           #! EA = L0x62c0a8 *)
bvAssign (rdx) (bvVar (L0x62c0a8));
(* adc    %rcx,%r11 *)
bvAdcC carry (r11) (bvVar (rcx)) (bvVar (r11)) (carry);
(* adc    %rbp,%r12 *)
bvAdcC carry (r12) (bvVar (rbp)) (bvVar (r12)) (carry);
(* adc    $0x0,%r13 *)
bvAdc (r13) (bvVar (r13)) (bvConst (fromPosZ 0%Z)) (carry);
(* xor    %r8,%r8 *)
bvAssign (r8) (bvConst (fromPosZ 0%Z));
bvAssign (carry) (bvConst (fromPosZ 0%Z));
bvAssign (overflow) (bvConst (fromPosZ 0%Z));
(* mulx   0x80(%rsi),%rcx,%rbp                     #! EA = L0x62c080 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c080)) (bvVar rdx);
(* adcx   %rcx,%r9 *)
bvAdcC carry (r9) (bvVar (rcx)) (bvVar (r9)) (carry);
(* adox   %rbp,%r10 *)
bvAdcC overflow (r10) (bvVar (rbp)) (bvVar (r10)) (overflow);
(* mulx   0x88(%rsi),%rcx,%rbp                     #! EA = L0x62c088 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c088)) (bvVar rdx);
(* adcx   %rcx,%r10 *)
bvAdcC carry (r10) (bvVar (rcx)) (bvVar (r10)) (carry);
(* adox   %rbp,%r11 *)
bvAdcC overflow (r11) (bvVar (rbp)) (bvVar (r11)) (overflow);
(* mulx   0x90(%rsi),%rcx,%rbp                     #! EA = L0x62c090 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c090)) (bvVar rdx);
(* adcx   %rcx,%r11 *)
bvAdcC carry (r11) (bvVar (rcx)) (bvVar (r11)) (carry);
(* adox   %rbp,%r12 *)
bvAdcC overflow (r12) (bvVar (rbp)) (bvVar (r12)) (overflow);
(* mulx   0x98(%rsi),%rcx,%rbp                     #! EA = L0x62c098 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c098)) (bvVar rdx);
(* mov    %r9,%rdx *)
bvAssign (rdx) (bvVar (r9));
(* adcx   %rcx,%r12 *)
bvAdcC carry (r12) (bvVar (rcx)) (bvVar (r12)) (carry);
(* shlx   %r14,%r9,%rcx *)
(* bvShl (rcx) (bvVar (r9)) (fromNat 32); *)
(* adox   %rbp,%r13 *)
bvAdcC overflow (r13) (bvVar (rbp)) (bvVar (r13)) (overflow);
(* shrx   %r14,%r9,%rbp *)
(* bvSplit (rbp) tmp (bvVar (r9)) (fromNat 32); *)
(* NOTE: merge 'shlx %r14,%r9,%rcx' with shrx %r14,%r9,%rbp' *)
bvSplit rbp rcx (bvVar r9) (fromNat 32);
bvShl rcx (bvVar rcx) (fromNat 32);
(* adcx   %r8,%r13 *)
bvAdcC carry (r13) (bvVar (r8)) (bvVar (r13)) (carry);
(* adox   %r8,%r8 *)
(* bvAdcC overflow (r8) (bvVar (r8)) (bvVar (r8)) (overflow); *)
(* NOTE: ignore overflow because it is zero *)
bvAdc (r8) (bvVar (r8)) (bvVar (r8)) (overflow);
(* adc    $0x0,%r8 *)
bvAdc (r8) (bvVar (r8)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rcx,%r10 *)
bvAddC carry (r10) (bvVar (rcx)) (bvVar (r10));
(* adc    %rbp,%r11 *)
bvAdcC carry (r11) (bvVar (rbp)) (bvVar (r11)) (carry);
(* mulx   %r15,%rcx,%rbp *)
bvMulf (rbp) (rcx) (bvVar (r15)) (bvVar rdx);
(* mov    0x10(%rbx),%rdx                          #! EA = L0x62c0b0 *)
bvAssign (rdx) (bvVar (L0x62c0b0));
(* adc    %rcx,%r12 *)
bvAdcC carry (r12) (bvVar (rcx)) (bvVar (r12)) (carry);
(* adc    %rbp,%r13 *)
bvAdcC carry (r13) (bvVar (rbp)) (bvVar (r13)) (carry);
(* adc    $0x0,%r8 *)
bvAdc (r8) (bvVar (r8)) (bvConst (fromPosZ 0%Z)) (carry);
(* xor    %r9,%r9 *)
bvAssign (r9) (bvConst (fromPosZ 0%Z));
bvAssign (carry) (bvConst (fromPosZ 0%Z));
bvAssign (overflow) (bvConst (fromPosZ 0%Z));
(* mulx   0x80(%rsi),%rcx,%rbp                     #! EA = L0x62c080 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c080)) (bvVar rdx);
(* adcx   %rcx,%r10 *)
bvAdcC carry (r10) (bvVar (rcx)) (bvVar (r10)) (carry);
(* adox   %rbp,%r11 *)
bvAdcC overflow (r11) (bvVar (rbp)) (bvVar (r11)) (overflow);
(* mulx   0x88(%rsi),%rcx,%rbp                     #! EA = L0x62c088 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c088)) (bvVar rdx);
(* adcx   %rcx,%r11 *)
bvAdcC carry (r11) (bvVar (rcx)) (bvVar (r11)) (carry);
(* adox   %rbp,%r12 *)
bvAdcC overflow (r12) (bvVar (rbp)) (bvVar (r12)) (overflow);
(* mulx   0x90(%rsi),%rcx,%rbp                     #! EA = L0x62c090 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c090)) (bvVar rdx);
(* adcx   %rcx,%r12 *)
bvAdcC carry (r12) (bvVar (rcx)) (bvVar (r12)) (carry);
(* adox   %rbp,%r13 *)
bvAdcC overflow (r13) (bvVar (rbp)) (bvVar (r13)) (overflow);
(* mulx   0x98(%rsi),%rcx,%rbp                     #! EA = L0x62c098 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c098)) (bvVar rdx);
(* mov    %r10,%rdx *)
bvAssign (rdx) (bvVar (r10));
(* adcx   %rcx,%r13 *)
bvAdcC carry (r13) (bvVar (rcx)) (bvVar (r13)) (carry);
(* shlx   %r14,%r10,%rcx *)
(* bvShl (rcx) (bvVar (r10)) (fromNat 32); *)
(* adox   %rbp,%r8 *)
bvAdcC overflow (r8) (bvVar (rbp)) (bvVar (r8)) (overflow);
(* shrx   %r14,%r10,%rbp *)
(* bvSplit (rbp) tmp (bvVar (r10)) (fromNat 32); *)
(* NOTE: merge 'shlx %r14,%r10,%rcx' with shrx %r14,%r10,%rbp' *)
bvSplit rbp rcx (bvVar r10) (fromNat 32);
bvShl rcx (bvVar rcx) (fromNat 32);
(* adcx   %r9,%r8 *)
bvAdcC carry (r8) (bvVar (r9)) (bvVar (r8)) (carry);
(* adox   %r9,%r9 *)
(* bvAdcC overflow (r9) (bvVar (r9)) (bvVar (r9)) (overflow); *)
(* NOTE: ignore overflow because it is zero *)
bvAdc (r9) (bvVar (r9)) (bvVar (r9)) (overflow);
(* adc    $0x0,%r9 *)
bvAdc (r9) (bvVar (r9)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rcx,%r11 *)
bvAddC carry (r11) (bvVar (rcx)) (bvVar (r11));
(* adc    %rbp,%r12 *)
bvAdcC carry (r12) (bvVar (rbp)) (bvVar (r12)) (carry);
(* mulx   %r15,%rcx,%rbp *)
bvMulf (rbp) (rcx) (bvVar (r15)) (bvVar rdx);
(* mov    0x18(%rbx),%rdx                          #! EA = L0x62c0b8 *)
bvAssign (rdx) (bvVar (L0x62c0b8));
(* adc    %rcx,%r13 *)
bvAdcC carry (r13) (bvVar (rcx)) (bvVar (r13)) (carry);
(* adc    %rbp,%r8 *)
bvAdcC carry (r8) (bvVar (rbp)) (bvVar (r8)) (carry);
(* adc    $0x0,%r9 *)
bvAdc (r9) (bvVar (r9)) (bvConst (fromPosZ 0%Z)) (carry);
(* xor    %r10,%r10 *)
bvAssign (r10) (bvConst (fromPosZ 0%Z));
bvAssign (carry) (bvConst (fromPosZ 0%Z));
bvAssign (overflow) (bvConst (fromPosZ 0%Z));
(* mulx   0x80(%rsi),%rcx,%rbp                     #! EA = L0x62c080 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c080)) (bvVar rdx);
(* adcx   %rcx,%r11 *)
bvAdcC carry (r11) (bvVar (rcx)) (bvVar (r11)) (carry);
(* adox   %rbp,%r12 *)
bvAdcC overflow (r12) (bvVar (rbp)) (bvVar (r12)) (overflow);
(* mulx   0x88(%rsi),%rcx,%rbp                     #! EA = L0x62c088 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c088)) (bvVar rdx);
(* adcx   %rcx,%r12 *)
bvAdcC carry (r12) (bvVar (rcx)) (bvVar (r12)) (carry);
(* adox   %rbp,%r13 *)
bvAdcC overflow (r13) (bvVar (rbp)) (bvVar (r13)) (overflow);
(* mulx   0x90(%rsi),%rcx,%rbp                     #! EA = L0x62c090 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c090)) (bvVar rdx);
(* adcx   %rcx,%r13 *)
bvAdcC carry (r13) (bvVar (rcx)) (bvVar (r13)) (carry);
(* adox   %rbp,%r8 *)
bvAdcC overflow (r8) (bvVar (rbp)) (bvVar (r8)) (overflow);
(* mulx   0x98(%rsi),%rcx,%rbp                     #! EA = L0x62c098 *)
bvMulf (rbp) (rcx) (bvVar (L0x62c098)) (bvVar rdx);
(* mov    %r11,%rdx *)
bvAssign (rdx) (bvVar (r11));
(* adcx   %rcx,%r8 *)
bvAdcC carry (r8) (bvVar (rcx)) (bvVar (r8)) (carry);
(* shlx   %r14,%r11,%rcx *)
(* bvShl (rcx) (bvVar (r11)) (fromNat 32); *)
(* adox   %rbp,%r9 *)
bvAdcC overflow (r9) (bvVar (rbp)) (bvVar (r9)) (overflow);
(* shrx   %r14,%r11,%rbp *)
(* bvSplit (rbp) tmp (bvVar (r11)) (fromNat 32); *)
(* NOTE: merge 'shlx %r14,%r11,%rcx' with shrx %r14,%r11,%rbp' *)
bvSplit rbp rcx (bvVar r11) (fromNat 32);
bvShl rcx (bvVar rcx) (fromNat 32);
(* adcx   %r10,%r9 *)
bvAdcC carry (r9) (bvVar (r10)) (bvVar (r9)) (carry);
(* adox   %r10,%r10 *)
(* bvAdcC overflow (r10) (bvVar (r10)) (bvVar (r10)) (overflow); *)
(* NOTE: ignore overflow because it is zero *)
bvAdc (r10) (bvVar (r10)) (bvVar (r10)) (overflow);
(* adc    $0x0,%r10 *)
bvAdc (r10) (bvVar (r10)) (bvConst (fromPosZ 0%Z)) (carry);
(* add    %rcx,%r12 *)
bvAddC carry (r12) (bvVar (rcx)) (bvVar (r12));
(* adc    %rbp,%r13 *)
bvAdcC carry (r13) (bvVar (rbp)) (bvVar (r13)) (carry);
(* mulx   %r15,%rcx,%rbp *)
bvMulf (rbp) (rcx) (bvVar (r15)) (bvVar rdx);
(* mov    %r12,%rbx *)
bvAssign (rbx) (bvVar (r12));
(* mov    -0xb93(%rip),%r14        # 0x427008      #! EA = L0x427008 *)
bvAssign (r14) (bvVar (L0x427008));
(* adc    %rcx,%r8 *)
bvAdcC carry (r8) (bvVar (rcx)) (bvVar (r8)) (carry);
(* mov    %r13,%rdx *)
bvAssign (rdx) (bvVar (r13));
(* adc    %rbp,%r9 *)
bvAdcC carry (r9) (bvVar (rbp)) (bvVar (r9)) (carry);
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
