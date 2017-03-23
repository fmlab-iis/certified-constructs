From Coq Require Import ZArith .
From mQhasm Require Import zDSL zRadix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope zdsl_scope.

Definition fe25519_add : program :=

let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in

let            y0 :=   5 in
let            y1 :=   6 in
let            y2 :=   7 in
let            y3 :=   8 in
let            y4 :=   9 in

let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let            r4 :=  24 in
[::
      (* # CPU: Intel(R) Xeon(R) CPU X5675 @ 3.07GHz *)
      (* # RAM: 32GB *)
      (* # Configuration: -c consts -s *)
      (* # With Boolector 1.6.0 (-minisat): 0m16.349s *)
      (*  *)
      (* int64 x0 *)
      (* int64 x1 *)
      (* int64 x2 *)
      (* int64 x3 *)
      (* int64 x4 *)
      (*  *)
      (* int64 y0 *)
      (* int64 y1 *)
      (* int64 y2 *)
      (* int64 y3 *)
      (* int64 y4 *)
      (*  *)
      (* int64 r0 *)
      (* int64 r1 *)
      (* int64 r2 *)
      (* int64 r3 *)
      (* int64 r4 *)
      (*  *)
      (* #// assume 0 <=u x0, x1, x2, x3, x4, y0, y1, y2, y3, y4 <=u 2**51 + 2**15 *)
      (*  *)
      (* r0 = x0 *)
zAssign r0 (zVar x0);
      (* r1 = x1 *)
zAssign r1 (zVar x1);
      (* r2 = x2 *)
zAssign r2 (zVar x2);
      (* r3 = x3 *)
zAssign r3 (zVar x3);
      (* r4 = x4 *)
zAssign r4 (zVar x4);
      (* r0 += y0 *)
zAssign r0 (zBinop zAdd (zVar r0) (zVar y0));
      (* r1 += y1 *)
zAssign r1 (zBinop zAdd (zVar r1) (zVar y1));
      (* r2 += y2 *)
zAssign r2 (zBinop zAdd (zVar r2) (zVar y2));
      (* r3 += y3 *)
zAssign r3 (zBinop zAdd (zVar r3) (zVar y3));
      (* r4 += y4 *)
zAssign r4 (zBinop zAdd (zVar r4) (zVar y4))
      (*  *)
      (* #// var sum_x = x0@u320 + x1@u320 * 2**51 + x2@u320 * 2**102 + x3@u320 * 2**153 + x4@u320 * 2**204 *)
      (* #//     sum_y = y0@u320 + y1@u320 * 2**51 + y2@u320 * 2**102 + y3@u320 * 2**153 + y4@u320 * 2**204 *)
      (* #//     sum_r = r0@u320 + r1@u320 * 2**51 + r2@u320 * 2**102 + r3@u320 * 2**153 + r4@u320 * 2**204 *)
      (* #// assert (sum_r - (sum_x + sum_y)) % (2**255 - 19) = 0 && *)
      (* #//        0 <=u r0, r1, r2, r3, r4 <u 2**53 *)
] .

Definition fe25519_add_inputs : VS.t :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            y0 :=   5 in
let            y1 :=   6 in
let            y2 :=   7 in
let            y3 :=   8 in
let            y4 :=   9 in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4; y0; y1; y2; y3; y4].

Definition fe25519_add_pre : bexp := zTrue.

Definition fe25519_add_post : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            y0 :=   5 in
let            y1 :=   6 in
let            y2 :=   7 in
let            y3 :=   8 in
let            y4 :=   9 in
let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let            r4 :=  24 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
zEqMod
  (
    (radix51 [::zVar x0; zVar x1; zVar x2; zVar x3; zVar x4])
    @+
    (radix51 [::zVar y0; zVar y1; zVar y2; zVar y3; zVar y4])
  )
  (radix51 [::zVar r0; zVar r1; zVar r2; zVar r3; zVar r4])
  (n25519).

Definition fe25519_add_spec :=
  {| spre := fe25519_add_pre;
     sprog := fe25519_add;
     spost := fe25519_add_post |}.

From mathcomp Require Import ssreflect eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_add : valid_ispec (fe25519_add_inputs, fe25519_add_spec).
Proof.
  time "valid_fe25519_add" verify_ispec.
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.
