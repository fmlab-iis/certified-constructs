From Coq Require Import ZArith .
From mQhasm Require Import zDSL zRadix .
From mathcomp Require Import seq .

Open Scope N_scope.
Open Scope zdsl_scope.

Definition fe25519_sq : program :=
let         wsize :=   64%positive in
let          qtwo :=   zConst (2%Z) in
let      pow2 x n := zBinop zMul x (zPow qtwo n) in

let            x0 :=   0 in (* *[uint64 *](xp +  0) *)
let            x1 :=   1 in (* *[uint64 *](xp +  8) *)
let            x2 :=   2 in (* *[uint64 *](xp + 16) *)
let            x3 :=   3 in (* *[uint64 *](xp + 24) *)
let            x4 :=   4 in (* *[uint64 *](xp + 32) *)

let            z0 :=   5 in (* *[uint64 *](rp +  0) *)
let            z1 :=   6 in (* *[uint64 *](rp +  8) *)
let            z2 :=   7 in (* *[uint64 *](rp + 16) *)
let            z3 :=   8 in (* *[uint64 *](rp + 24) *)
let            z4 :=   9 in (* *[uint64 *](rp + 32) *)

let            r0 :=  20 in
let            r1 :=  21 in
let            r2 :=  22 in
let            r3 :=  23 in
let            r4 :=  24 in

let            c1 :=  31 in
let            c2 :=  32 in
let            c3 :=  33 in
let            c4 :=  34 in
let            c5 :=  35 in
let            c6 :=  36 in
let            c7 :=  37 in

let          x119 :=  41 in
let          x219 :=  42 in
let          x319 :=  43 in
let          x419 :=  44 in

let           r01 :=  50 in
let           r11 :=  51 in
let           r21 :=  52 in
let           r31 :=  53 in
let           r41 :=  54 in
let           rax :=  55 in
let           rdx :=  56 in

let             t :=  60 in
let       redmask :=  61 in

let           tmp := 998 in
let         carry := 999 in

[::
      (*  *)
      (* int64 rp *)
      (* int64 xp *)
      (*  *)
      (* input rp *)
      (* input xp *)
      (*  *)
      (* int64 r0 *)
      (* int64 r1 *)
      (* int64 r2 *)
      (* int64 r3 *)
      (* int64 r4 *)
      (*  *)
      (* int64 c1 *)
      (* int64 c2 *)
      (* int64 c3 *)
      (* int64 c4 *)
      (* int64 c5 *)
      (* int64 c6 *)
      (* int64 c7 *)
      (* caller c1 *)
      (* caller c2 *)
      (* caller c3 *)
      (* caller c4 *)
      (* caller c5 *)
      (* caller c6 *)
      (* caller c7 *)
      (* stack64 c1_stack *)
      (* stack64 c2_stack *)
      (* stack64 c3_stack *)
      (* stack64 c4_stack *)
      (* stack64 c5_stack *)
      (* stack64 c6_stack *)
      (* stack64 c7_stack *)
      (* stack64 x119_stack *)
      (* stack64 x219_stack *)
      (* stack64 x319_stack *)
      (* stack64 x419_stack *)
      (*  *)

      (* #required for  macro *)

      (* int64 r01 *)
      (* int64 r11 *)
      (* int64 r21 *)
      (* int64 r31 *)
      (* int64 r41 *)
      (* int64 rax *)
      (* int64 rdx *)

      (* int64 t *)
      (* int64 redmask *)

      (*  *)
      (* enter fe25519_sq *)
      (*  *)
      (* c1_stack = c1 *)
      (* c2_stack = c2 *)
      (* c3_stack = c3 *)
      (* c4_stack = c4 *)
      (* c5_stack = c5 *)
      (* c6_stack = c6 *)
      (* c7_stack = c7 *)
      (*  *)
      (*   #BEGIN MACRO  *)
      (*   rax = *[uint64 *](xp + 0) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 0) *)
      (*   r0 = rax *)
      (*   r01 = rdx *)
zAssign rax (zVar x0);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x0)) wsize;
zAssign r0 (zVar rax);
zAssign r01 (zVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
      (*   r1 = rax *)
      (*   r11 = rdx *)
zAssign rax (zVar x0);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x1)) wsize;
zAssign r1 (zVar rax);
zAssign r11 (zVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   r2 = rax *)
      (*   r21 = rdx *)
zAssign rax (zVar x0);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x2)) wsize;
zAssign r2 (zVar rax);
zAssign r21 (zVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   r3 = rax *)
      (*   r31 = rdx *)
zAssign rax (zVar x0);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x3)) wsize;
zAssign r3 (zVar rax);
zAssign r31 (zVar rdx);
      (*   rax = *[uint64 *](xp + 0) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   r4 = rax *)
      (*   r41 = rdx *)
zAssign rax (zVar x0);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r4 (zVar rax);
zAssign r41 (zVar rdx);
      (*  *)
      (*   rax = *[uint64 *](xp + 8) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 8) *)
      (*   carry? r2 += rax *)
      (*   r21 += rdx + carry *)
zAssign rax (zVar x1);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x1)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar rax));
zSplit carry r2 (zVar r2) wsize;
zAssign r21 (zBinop zAdd (zVar r21) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   carry? r3 += rax *)
      (*   r31 += rdx + carry *)
zAssign rax (zVar x1);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x2)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar rax));
zSplit carry r3 (zVar r3) wsize;
zAssign r31 (zBinop zAdd (zVar r31) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax <<= 1 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r4 += rax *)
      (*   r41 += rdx + carry *)
zAssign rax (zVar x1);
zAssign rax (zBinop zMul (zVar rax) qtwo);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x3)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar rax));
zSplit carry r4 (zVar r4) wsize;
zAssign r41 (zBinop zAdd (zVar r41) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 8) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r0 += rax *)
      (*   r01 += rdx + carry *)
zAssign rax (zVar x1);
zAssign rax (zBinop zMul (zVar rax) (zConst 38%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar rax));
zSplit carry r0 (zVar r0) wsize;
zAssign r01 (zBinop zAdd (zVar r01) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 16) *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 16) *)
      (*   carry? r4 += rax *)
      (*   r41 += rdx + carry *)
zAssign rax (zVar x2);
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x2)) wsize;
zAssign r4 (zBinop zAdd (zVar r4) (zVar rax));
zSplit carry r4 (zVar r4) wsize;
zAssign r41 (zBinop zAdd (zVar r41) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 16) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r0 += rax *)
      (*   r01 += rdx + carry *)
zAssign rax (zVar x2);
zAssign rax (zBinop zMul (zVar rax) (zConst 38%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x3)) wsize;
zAssign r0 (zBinop zAdd (zVar r0) (zVar rax));
zSplit carry r0 (zVar r0) wsize;
zAssign r01 (zBinop zAdd (zVar r01) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 16) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r1 += rax *)
      (*   r11 += rdx + carry *)
zAssign rax (zVar x2);
zAssign rax (zBinop zMul (zVar rax) (zConst 38%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar rax));
zSplit carry r1 (zVar r1) wsize;
zAssign r11 (zBinop zAdd (zVar r11) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 24) *)
      (*   rax *= 19 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 24) *)
      (*   carry? r1 += rax *)
      (*   r11 += rdx + carry *)
zAssign rax (zVar x3);
zAssign rax (zBinop zMul (zVar rax) (zConst 19%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x3)) wsize;
zAssign r1 (zBinop zAdd (zVar r1) (zVar rax));
zSplit carry r1 (zVar r1) wsize;
zAssign r11 (zBinop zAdd (zVar r11) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*   rax = *[uint64 *](xp + 24) *)
      (*   rax *= 38 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r2 += rax *)
      (*   r21 += rdx + carry *)
zAssign rax (zVar x3);
zAssign rax (zBinop zMul (zVar rax) (zConst 38%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r2 (zBinop zAdd (zVar r2) (zVar rax));
zSplit carry r2 (zVar r2) wsize;
zAssign r21 (zBinop zAdd (zVar r21) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*    *)
      (*   rax = *[uint64 *](xp + 32) *)
      (*   rax *= 19 *)
      (*   (uint128) rdx rax = rax * *[uint64 *](xp + 32) *)
      (*   carry? r3 += rax *)
      (*   r31 += rdx + carry *)
zAssign rax (zVar x4);
zAssign rax (zBinop zMul (zVar rax) (zConst 19%Z));
zSplit rdx rax (zBinop zMul (zVar rax) (zVar x4)) wsize;
zAssign r3 (zBinop zAdd (zVar r3) (zVar rax));
zSplit carry r3 (zVar r3) wsize;
zAssign r31 (zBinop zAdd (zVar r31) (zBinop zAdd (zVar rdx) (zVar carry)));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   redmask = *[uint64 *] &crypto_sign_ed25519_amd64_51_REDMASK51 *)
      (*   r01 = (r01.r0) << 13 *)
      (*   r0 &= redmask *)
zSplit tmp r0 (zVar r0) 51%positive;
zAssign r01 (zBinop zAdd (pow2 (zVar r01) 13%positive) (zVar tmp));
      (*    *)
      (*   r11 = (r11.r1) << 13 *)
      (*   r1 &= redmask *)
      (*   r1 += r01 *)
zSplit tmp r1 (zVar r1) 51%positive;
zAssign r11 (zBinop zAdd (pow2 (zVar r11) 13%positive) (zVar tmp));
zAssign r1 (zBinop zAdd (zVar r1) (zVar r01));
      (*    *)
      (*   r21 = (r21.r2) << 13 *)
      (*   r2 &= redmask *)
      (*   r2 += r11 *)
zSplit tmp r2 (zVar r2) 51%positive;
zAssign r21 (zBinop zAdd (pow2 (zVar r21) 13%positive) (zVar tmp));
zAssign r2 (zBinop zAdd (zVar r2) (zVar r11));
      (*    *)
      (*   r31 = (r31.r3) << 13 *)
      (*   r3 &= redmask *)
      (*   r3 += r21 *)
zSplit tmp r3 (zVar r3) 51%positive;
zAssign r31 (zBinop zAdd (pow2 (zVar r31) 13%positive) (zVar tmp));
zAssign r3 (zBinop zAdd (zVar r3) (zVar r21));
      (*    *)
      (*   r41 = (r41.r4) << 13 *)
      (*   r4 &= redmask *)
      (*   r4 += r31 *)
zSplit tmp r4 (zVar r4) 51%positive;
zAssign r41 (zBinop zAdd (pow2 (zVar r41) 13%positive) (zVar tmp));
zAssign r4 (zBinop zAdd (zVar r4) (zVar r31));
      (*   r41 = r41 * 19 *)
zAssign r41 (zBinop zMul (zVar r41) (zConst 19%Z));
      (*   r0 += r41 *)
zAssign r0 (zBinop zAdd (zVar r0) (zVar r41));
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (*   t = r0 *)
      (*   (uint64) t >>= 51 *)
      (*   t += r1 *)
      (*   r0 &= redmask *)
zAssign t (zVar r0);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zAdd (zVar t) (zVar r1));
zAssign r0 (zVar tmp);
      (*    *)
      (*   r1 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r2 *)
      (*   r1 &= redmask *)
zAssign r1 (zVar t);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zAdd (zVar t) (zVar r2));
zAssign r1 (zVar tmp);
      (*    *)
      (*   r2 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r3 *)
      (*   r2 &= redmask *)
zAssign r2 (zVar t);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zAdd (zVar t) (zVar r3));
zAssign r2 (zVar tmp);
      (*    *)
      (*   r3 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t += r4 *)
      (*   r3 &= redmask *)
zAssign r3 (zVar t);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zAdd (zVar t) (zVar r4));
zAssign r3 (zVar tmp);
      (*    *)
      (*   r4 = t *)
      (*   (uint64) t >>= 51 *)
      (*   t *= 19 *)
      (*   r0 += t *)
      (*   r4 &= redmask *)
zAssign r4 (zVar t);
zSplit t tmp (zVar t) (51%positive);
zAssign t (zBinop zMul (zVar t) (zConst 19%Z));
zAssign r0 (zBinop zAdd (zVar r0) (zVar t));
zAssign r4 (zVar tmp);
      (*   #END MACRO  *)
      (*  *)
      (*  *)
      (*  *)
      (*  *)
      (* *[uint64 *](rp + 0) = r0 *)
zAssign z0 (zVar r0);
      (* *[uint64 *](rp + 8) = r1 *)
zAssign z1 (zVar r1);
      (* *[uint64 *](rp + 16) = r2 *)
zAssign z2 (zVar r2);
      (* *[uint64 *](rp + 24) = r3 *)
zAssign z3 (zVar r3);
      (* *[uint64 *](rp + 32) = r4 *)
zAssign z4 (zVar r4)
      (*   *)
      (*  *)
      (* c1 =c1_stack *)
      (* c2 =c2_stack *)
      (* c3 =c3_stack *)
      (* c4 =c4_stack *)
      (* c5 =c5_stack *)
      (* c6 =c6_stack *)
      (* c7 =c7_stack *)
      (*  *)
      (* leave *)
] .

Definition fe25519_sq_inputs : VS.t :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4].

Definition fe25519_sq_pre : bexp := zTrue.

Definition fe25519_sq_post : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            z0 :=   5 in
let            z1 :=   6 in
let            z2 :=   7 in
let            z3 :=   8 in
let            z4 :=   9 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
zEqMod
  (
    zPow (radix51 [::zVar x0; zVar x1; zVar x2; zVar x3; zVar x4]) 2
  )
  (radix51 [::zVar z0; zVar z1; zVar z2; zVar z3; zVar z4])
  (n25519).

Definition fe25519_sq_spec :=
  {| spre := fe25519_sq_pre;
     sprog := fe25519_sq;
     spost := fe25519_sq_post |}.

From mathcomp Require Import eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_sq : valid_ispec (fe25519_sq_inputs, fe25519_sq_spec).
Proof.
  time "valid_fe25519_sq" verify_ispec.
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.

