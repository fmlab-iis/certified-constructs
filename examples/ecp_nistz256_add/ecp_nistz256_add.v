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
let L0x62c080 := 7 in  (* ap *)
let L0x62c088 := 1 in
let L0x62c090 := 6 in
let L0x62c098 := 0 in

let L0x62c0a0 := 10 in (* bp *)
let L0x62c0a8 := 12 in
let L0x62c0b0 := 9 in
let L0x62c0b8 := 2 in

let L0x427000 := 11 in (* p0 *)

let r10 := 3 in
let r11 := 4 in
let r8 := 5 in
let r9 := 8 in
let r13 := 13 in

let rdx := 100 in
let rax := 101 in
let rsi := 102 in
let carry := 999 in

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

[::

bvAssign L0x62c080 (bvVar a0);
bvAssign L0x62c088 (bvVar a1);
bvAssign L0x62c090 (bvVar a2);
bvAssign L0x62c098 (bvVar a3);

bvAssign L0x62c0a0 (bvVar b0);
bvAssign L0x62c0a8 (bvVar b1);
bvAssign L0x62c0b0 (bvVar b2);
bvAssign L0x62c0b8 (bvVar b3);

bvAssign L0x427000 (bvConst (fromPosZ p0));
   
(* mov    (%rsi),%r8                               #! EA = L0x62c080 *)
bvAssign (r8) (bvVar (L0x62c080));
(* xor    %r13,%r13 *)
bvAssign (r13) (bvConst (fromPosZ 0%Z));
(* mov    0x8(%rsi),%r9                            #! EA = L0x62c088 *)
bvAssign (r9) (bvVar (L0x62c088));
(* mov    0x10(%rsi),%r10                          #! EA = L0x62c090 *)
bvAssign (r10) (bvVar (L0x62c090));
(* mov    0x18(%rsi),%r11                          #! EA = L0x62c098 *)
bvAssign (r11) (bvVar (L0x62c098));
(* lea    -0x2fd(%rip),%rsi        # 0x427000      #! EA = L0x427000 *)
bvAssign (rsi) (bvVar (L0x427000));
(* add    (%rdx),%r8                               #! EA = L0x62c0a0 *)
bvAddC carry (r8) (bvVar (L0x62c0a0)) (bvVar (r8));
(* adc    0x8(%rdx),%r9                            #! EA = L0x62c0a8 *)
bvAdcC carry (r9) (bvVar (L0x62c0a8)) (bvVar (r9)) (carry);
(* mov    %r8,%rax *)
bvAssign (rax) (bvVar (r8));
(* adc    0x10(%rdx),%r10                          #! EA = L0x62c0b0 *)
bvAdcC carry (r10) (bvVar (L0x62c0b0)) (bvVar (r10)) (carry);
(* adc    0x18(%rdx),%r11                          #! EA = L0x62c0b8 *)
bvAdcC carry (r11) (bvVar (L0x62c0b8)) (bvVar (r11)) (carry);
(* mov    %r9,%rdx *)
bvAssign (rdx) (bvVar (r9));
(* adc    $0x0,%r13 *)
bvAdc (r13) (bvVar (r13)) (bvConst (fromPosZ 0%Z)) (carry);

bvAssign t0 (bvVar r8);
bvAssign t1 (bvVar r9);
bvAssign t2 (bvVar r10);
bvAssign t3 (bvVar r11);
bvAssign t4 (bvVar r13)
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
         +e
         (radix64 [::bvevar b0; bvevar b1; bvevar b2; bvevar b3])
       )

       (
         (radix64 [::bvevar t0; bvevar t1; bvevar t2; bvevar t3;
                     bvevar t4])
       )    

       (
         (radix64 [::bvconst p0; bvconst p1; bvconst p2; bvconst p3])
       )
    ]
    [::
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
