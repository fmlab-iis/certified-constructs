From Coq Require Import ZArith .
From mQhasm Require Import zDSL zRadix .
From mathcomp Require Import seq .

(* This is an alternative implementation of fe25519_mul121666. *)

Open Scope N_scope.
Open Scope zdsl_scope.

Definition fe25519_mul121666 : program :=

let          qtwo :=   zConst 2%Z in
let         wsize :=   64%positive in

let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in

let            r0 :=  10 in
let            r1 :=  11 in
let            r2 :=  12 in
let            r3 :=  13 in
let            r4 :=  14 in

let           rax :=  20 in
let           rdx :=  21 in

[::
zAssign rax (zVar x0);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r0 (zVar rax);
zAssign r1 (zVar rdx);
      (*    *)
zAssign rax (zVar x1);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r1 (zBinop zAdd (zVar r1) (zVar rax));
zAssign r2 (zVar rdx);
      (*    *)
zAssign rax (zVar x2);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r2 (zBinop zAdd (zVar r2) (zVar rax));
zAssign r3 (zVar rdx);
      (*    *)
zAssign rax (zVar x3);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r3 (zBinop zAdd (zVar r3) (zVar rax));
zAssign r4 (zVar rdx);
      (*    *)
zAssign rax (zVar x4);
zSplit rdx rax (zBinop zMul (zVar rax) (zConst 121666)) 51;
zAssign r4 (zBinop zAdd (zVar r4) (zVar rax));
zAssign rdx (zBinop zMul (zVar rdx) (zConst 19));
zAssign r0 (zBinop zAdd (zVar r0) (zVar rdx))
] .

Definition fe25519_mul121666_inputs : VS.t :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
VSLemmas.OP.P.of_list [:: x0; x1; x2; x3; x4].

Definition fe25519_mul121666_pre : bexp := zTrue.

Definition fe25519_mul121666_post : bexp :=
let            x0 :=   0 in
let            x1 :=   1 in
let            x2 :=   2 in
let            x3 :=   3 in
let            x4 :=   4 in
let            r0 :=  10 in
let            r1 :=  11 in
let            r2 :=  12 in
let            r3 :=  13 in
let            r4 :=  14 in
let        n25519 := 57896044618658097711785492504343953926634992332820282019728792003956564819949%positive in
zEqMod
  (
    (radix51 [::zVar x0; zVar x1; zVar x2; zVar x3; zVar x4])
    @*
    (zConst 121666)
  )
  (radix51 [::zVar r0; zVar r1; zVar r2; zVar r3; zVar r4])
  (n25519).

Definition fe25519_mul121666_spec :=
  {| spre := fe25519_mul121666_pre;
     sprog := fe25519_mul121666;
     spost := fe25519_mul121666_post |}.

From mathcomp Require Import ssreflect eqtype ssrbool.
From mQhasm Require Import Verify.

Lemma valid_fe25519_mul121666 : valid_ispec (fe25519_mul121666_inputs, fe25519_mul121666_spec).
Proof.
  time "valid_fe25519_mul121666" verify_ispec.
Qed.

Close Scope zdsl_scope.
Close Scope N_scope.
