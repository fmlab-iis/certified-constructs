
From Coq Require Import OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From Common Require Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Section NatLemmas.

  Lemma subn_gtn : forall n m r, n < m - r -> r < m.
  Proof.
    move=> n m r H.
    have: r < m.
    - rewrite -(subn_gt0 r m).
      induction n.
      + assumption.
      + by auto.
    - exact.
  Qed.

  Lemma lt_subr_addl : forall n m r : nat, (n < m - r) == (n + r < m).
  Proof.
    move=> n m r.
    case Hrm: (r < m).
    - rewrite -(ltn_add2r r n (m - r)).
      rewrite (subnK (ltnW Hrm)).
      exact: eqxx.
    - (* left is false *)
      move/negP/negP: (Hrm) => Hle.
      rewrite -leqNgt in Hle.
      move: (subn_eq0 m r) => Hsub.
      rewrite Hle in Hsub.
      move/idP/eqP: Hsub => Hsub.
      rewrite Hsub => {Hsub}.
      rewrite ltn0.
      (* right is false *)
      rewrite -(leq_add2l n m r) in Hle.
      move: (leq_trans (leq_addl n m) Hle) => {Hle} Hle.
      rewrite (leqNgt m (n + r)) in Hle.
      move/negPf: Hle => Hle.
      rewrite Hle.
      exact: eqxx.
  Qed.

  Lemma lt_sub1r_add1l : forall n m : nat, (n < m.-1) == (n.+1 < m).
  Proof.
    move=> n m.
    rewrite -{2}addn1 -subn1.
    exact: (lt_subr_addl n m 1).
  Qed.

  Lemma addr_subK : forall n m : nat, n + m - m = n.
  Proof.
    move=> n; elim: n.
    - move=> m.
      rewrite add0n subnn.
      reflexivity.
    - move=> n IH m.
      rewrite -(addnA 1 n m) -addnBA.
      + rewrite IH.
        reflexivity.
      + exact: leq_addl.
  Qed.

  Lemma addl_subK : forall n m : nat, m + n - m = n.
  Proof.
    move=> n m.
    rewrite addnC.
    exact: addr_subK.
  Qed.

  Lemma gt0_sub1F :
    forall n : nat, n > 0 -> n = n - 1 -> False.
  Proof.
    move=> n; elim: n.
    - done.
    - move=> n IH Hgt Heq.
      rewrite -add1n addl_subK add1n in Heq.
      apply: IH.
      + rewrite -Heq.
        assumption.
      + rewrite -{2}Heq -add1n addl_subK.
        reflexivity.
  Qed.

  Lemma ltn_leq_trans n m p :
    m < n -> n <= p -> m < p.
  Proof.
    move=> Hmn Hnp.
    move/ltP: Hmn => Hmn.
    move/leP: Hnp => Hnp.
    apply/ltP.
    exact: (Lt.lt_le_trans _ _ _ Hmn Hnp).
  Qed.

End NatLemmas.



(** EQTYPE modules. *)

Module NatEqtype <: EQTYPE.
  Definition t := nat_eqType.
End NatEqtype.

Module OptionNatEqtype <: EQTYPE.
  Module OptionNat := MakeOptionReflectable(NatEqtype).
  Definition t := OptionNat.option_eqType.
End OptionNatEqtype.



(** An ordered type for nat with a Boolean equality in mathcomp. *)

Module NatOrderMinimal <: SsrOrderedTypeMinimal.

  Definition t : eqType := nat_eqType.

  Definition eq : t -> t -> bool := fun x y : t => x == y.

  Definition lt : t -> t -> bool := fun x y => x < y.

  Hint Unfold eq lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> x y z.
    exact: ltn_trans.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    move=> x y Hlt.
    apply/negP => Heq.
    apply/idP: Hlt.
    by rewrite /lt (eqP Heq) ltnn.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    case H: (Nat.compare x y).
    - apply: EQ.
      move: (PeanoNat.Nat.compare_eq_iff x y) => [Hc _].
      apply/eqP.
      exact: (Hc H).
    - apply: LT.
      move: (PeanoNat.Nat.compare_lt_iff x y) => [Hc _].
      apply/ltP.
      exact: (Hc H).
    - apply: GT.
      move: (PeanoNat.Nat.compare_gt_iff x y) => [Hc _].
      apply/ltP.
      exact: (Hc H).
  Defined.

End NatOrderMinimal.

Module NatOrder <: SsrOrderedType := MakeSsrOrderedType NatOrderMinimal.
