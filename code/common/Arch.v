
(** * Machine architectures *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.

Module Type ARCH.
  Parameter wordsize : nat.
  Parameter wordsize_positive : wordsize > 0.
End ARCH.

Module AMD64 <: ARCH.
  Definition wordsize : nat := 64.
  Lemma wordsize_positive : wordsize > 0.
  Proof.
    exact: eqxx.
  Qed.
End AMD64.

Module X86 <: ARCH.
  Definition wordsize : nat := 32.
  Lemma wordsize_positive : wordsize > 0.
  Proof.
    exact: eqxx.
  Qed.
End X86.
