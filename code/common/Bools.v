
From mathcomp Require Import ssreflect ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma and_true_l :
  forall a b : bool, a && b = true -> a = true.
Proof.
  move=>a; by elim: a.
Qed.

Lemma and_true_r :
  forall a b : bool, a && b = true -> b = true.
Proof.
  move=>a; by elim: a.
Qed.

Lemma and_true :
  forall a b : bool, a && b = true -> a = true /\ b = true.
Proof.
  move=>a; by elim: a.
Qed.

Lemma and_false :
  forall a b : bool, a && b = false -> a = false \/ b = false.
Proof.
  move=> a b /nandP H.
  case: H => H.
  - left; exact: (negbTE H).
  - right; exact: (negbTE H).
Qed.