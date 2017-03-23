
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Common Require Import Types ZAriths.
From mQhasm Require Import zDSL.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope Z_scope.



Definition radix51 := limbs 51.

Lemma zpos_25519 :
  Z.pos (2^255 - 19) = 2^255 - 19.
Proof.
  reflexivity.
Qed.

Lemma radix51_25519_reduction x :
  modulo (x * 2^255) (x * 19) (2^255 - 19).
Proof.
  exists x.
  ring.
Qed.

Lemma radix51_25519_plus_reduction255 x y :
  modulo (y + x * 2^255) (y + x * 19) (2^255 - 19).
Proof.
  exists x.
  ring.
Qed.

Lemma radix51_25519_plus_reduction306 x y :
  modulo (y * 2^51 + x * 2^306) ((y + x * 19) * 2^51) (2^255 - 19).
Proof.
  exists (x * 2^51).
  ring.
Qed.

Lemma radix51_25519_plus_reduction357 x y :
  modulo (y * 2^102 + x * 2^357) ((y + x * 19) * 2^102) (2^255 - 19).
Proof.
  exists (x * 2^102).
  ring.
Qed.

Lemma radix51_25519_plus_reduction408 x y :
  modulo (y * 2^153 + x * 2^408) ((y + x * 19) * 2^153) (2^255 - 19).
Proof.
  exists (x * 2^153).
  ring.
Qed.

Lemma radix51_25519_plus_reduction459 x y :
  modulo (y * 2^204 + x * 2^459) ((y + x * 19) * 2^204) (2^255 - 19).
Proof.
  exists (x * 2^204).
  ring.
Qed.
