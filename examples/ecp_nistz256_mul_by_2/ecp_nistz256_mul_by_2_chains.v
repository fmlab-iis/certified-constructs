From Coq Require Import ZArith .
From mathcomp Require Import ssreflect ssrbool ssrnat seq .
From Common Require Import Bits .
From mQhasm Require Import bvDSL bvVerify Options .
Set Implicit Arguments .
Unset Strict Implicit .
Import Prenex Implicits .
Open Scope N_scope.
Open Scope bvdsl_scope.

Definition radix64 := @limbs 64 .

Definition check_inputs : VS.t :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
  VSLemmas.OP.P.of_list [:: a0; a1; a2; a3 ].

Definition check_pre : bexp :=
  bvrands [::] .

Definition nistz256_mul_by_2_post : bexp :=
  let  a0 := 1000 in
  let  a1 := 1001 in
  let  a2 := 1002 in
  let  a3 := 1003 in
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
         (bvconst 2)
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

Definition program :=

let L0x62c080 := 8 in
let L0x62c088 := 2 in
let L0x62c090 := 7 in
let L0x62c098 := 1 in

let L0x427000 := 12 in

let rax := 13 in
let rcx := 11 in
let rdx := 10 in
let rsi := 14 in
let r8 := 6 in
let r9 := 9 in
let r10 := 4 in
let r11 := 5 in
let r12 := 0 in
let r13 := 3 in

let carry := 999 in

let a0 := 1000 in
let a1 := 1001 in
let a2 := 1002 in
let a3 := 1003 in
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

bvAssign L0x427000 (bvConst (fromPosZ p0));

(* mov    (%rsi),%r8                               #! EA = L0x62c080 *)
bvAssign r8 (bvVar L0x62c080);
(* xor    %r13,%r13 *)
bvAssign r13 (bvConst (fromPosZ 0%Z));
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    0x8(%rsi),%r9                            #! EA = L0x62c088 *)
bvAssign r9 (bvVar L0x62c088);
(* add    %r8,%r8 *)
bvAddC carry r8 (bvVar r8) (bvVar r8);
(* mov    0x10(%rsi),%r10                          #! EA = L0x62c090 *)
bvAssign r10 (bvVar L0x62c090);
(* adc    %r9,%r9 *)
bvAdcC carry r9 (bvVar r9) (bvVar r9) carry;
(* mov    0x18(%rsi),%r11                          #! EA = L0x62c098 *)
bvAssign r11 (bvVar L0x62c098);
(* lea    -0xe3(%rip),%rsi        # 0x427000       #! EA = L0x427000 *)
bvAssign rsi (bvVar L0x427000);
(* mov    %r8,%rax *)
bvAssign rax (bvVar r8);
(* adc    %r10,%r10 *)
bvAdcC carry r10 (bvVar r10) (bvVar r10) carry;
(* adc    %r11,%r11 *)
bvAdcC carry r11 (bvVar r11) (bvVar r11) carry;
(* mov    %r9,%rdx *)
bvAssign rdx (bvVar r9);
(* adc    $0x0,%r13 *)
(* bvAdcC carry r13 (bvConst (fromPosZ 0%Z)) (bvVar r13) carry; *)
(* NOTE: ignore carry because it is zero *)
bvAdc r13 (bvConst (fromPosZ 0%Z)) (bvVar r13) carry;
bvAssign carry (bvConst (fromPosZ 0%Z));
(* mov    %r10,%rcx *)
bvAssign rcx (bvVar r10);
(* mov    %r11,%r12 *)
bvAssign r12 (bvVar r11);

bvAssign t0 (bvVar rax);
bvAssign t1 (bvVar rdx);
bvAssign t2 (bvVar rcx);
bvAssign t3 (bvVar r12);
bvAssign t4 (bvVar r13)
].

Definition nistz256_mul_by_2_spec :=
  {| spre := check_pre;
     sprog := program;
     spost := nistz256_mul_by_2_post |}.

Lemma valid_nistz256_mul_mont :
  valid_bvspec (check_inputs, nistz256_mul_by_2_spec).
Proof.
  time "valid_nistz256_mul_by_2" verify_bvspec .
Qed.

Close Scope bvdsl_scope.
Close Scope N_scope.
