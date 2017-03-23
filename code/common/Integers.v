
From Coq Require Import ZArith OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat ssralg ssrfun choice eqtype.
From CompCert Require Import Integers.
From Common Require Import Bits Types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Byte, int, and int64 are eqTypes. *)

Definition byte_eq : byte -> byte -> bool := Byte.eq.
Definition int_eq : int -> int -> bool := Int.eq.
Definition int64_eq : int64 -> int64 -> bool := Int64.eq.

Ltac prove_int_eqtype :=
  let eq :=
      match goal with
      | |- Equality.axiom byte_eq => byte_eq
      | |- Equality.axiom int_eq => int_eq
      | |- Equality.axiom int64_eq => int64_eq
      | |- _ => fail
      end in
  let meq :=
      match goal with
      | |- Equality.axiom byte_eq => Byte.eq
      | |- Equality.axiom int_eq => Int.eq
      | |- Equality.axiom int64_eq => Int64.eq
      | |- _ => fail
      end in
  let unsigned :=
      match goal with
      | |- Equality.axiom byte_eq => Byte.unsigned
      | |- Equality.axiom int_eq => Int.unsigned
      | |- Equality.axiom int64_eq => Int64.unsigned
      | |- _ => fail
      end in
  let repr :=
      match goal with
      | |- Equality.axiom byte_eq => Byte.repr
      | |- Equality.axiom int_eq => Int.repr
      | |- Equality.axiom int64_eq => Int64.repr
      | |- _ => fail
      end in
  let repr_unsigned :=
      match goal with
      | |- Equality.axiom byte_eq => Byte.repr_unsigned
      | |- Equality.axiom int_eq => Int.repr_unsigned
      | |- Equality.axiom int64_eq => Int64.repr_unsigned
      | |- _ => fail
      end in
  let n := fresh "n" in
  let m := fresh "m" in
  let H := fresh "H" in
  let Hnm := fresh "Hnm" in
  rewrite /eq /meq /Coqlib.zeq => n m;
  case: (Z.eq_dec (unsigned n) (unsigned m)) => H;
  [
    apply: ReflectT;
    have: repr (unsigned n) = repr (unsigned m);
    [
      rewrite H; reflexivity |
      rewrite 2!repr_unsigned; move=> Hnm; exact: Hnm
    ] |
    apply: ReflectF; move=> Hnm; apply: H; rewrite Hnm; reflexivity
  ].

Lemma byte_eqP : Equality.axiom byte_eq.
Proof.
  prove_int_eqtype.
Qed.

Canonical byte_eqMixin := EqMixin byte_eqP.
Canonical byte_eqType := Eval hnf in EqType byte byte_eqMixin.

Lemma int_eqP : Equality.axiom int_eq.
Proof.
  prove_int_eqtype.
Qed.

Canonical int_eqMixin := EqMixin int_eqP.
Canonical int_eqType := Eval hnf in EqType int int_eqMixin.

Lemma int64_eqP : Equality.axiom int64_eq.
Proof.
  prove_int_eqtype.
Qed.

Canonical int64_eqMixin := EqMixin int64_eqP.
Canonical int64_eqType := Eval hnf in EqType int64 int64_eqMixin.

Module ByteEqtype <: EQTYPE.
  Definition t := byte_eqType.
End ByteEqtype.

Module IntEqtype <: EQTYPE.
  Definition t := int_eqType.
End IntEqtype.

Module Int64Eqtype <: EQTYPE.
  Definition t := int64_eqType.
End Int64Eqtype.



(** Conversion from hex strings to CompCert integers. *)

Section HexStrings.

  From Coq Require Import Ascii.

  Lemma bits_range n (x : BITS n) : (-1 < toPosZ x < two_p (Z.of_nat n))%Z.
  Proof.
    split.
    - apply: (Z.lt_le_trans _ 0).
      + done.
      + exact: toPosZ_min.
    - rewrite two_p_correct -two_power_nat_equiv.
      exact: toPosZ_max.
  Qed.

  Definition byte_of_bits8 (n : BITS 8) : byte :=
    {| Byte.intval := toPosZ n; Byte.intrange := bits_range n |}.

  Definition int_of_bits32 (n : BITS 32) : int :=
    {| Int.intval := toPosZ n; Int.intrange := bits_range n |}.

  Definition int64_of_bits64 (n : BITS 64) : int64 :=
    {| Int64.intval := toPosZ n; Int64.intrange := bits_range n |}.

  Definition byte_of_hex (str : 2.-string) : byte :=
    byte_of_bits8 (fromNString str).

  Definition int_of_hex (str : 8.-string) : int :=
    int_of_bits32 (fromNString str).

  Definition int64_of_hex (str : 16.-string) : int64 :=
    int64_of_bits64 (fromNString str).

End HexStrings.



(** Ordered types for byte, int, and int64 *)

Lemma byte_unsigned_inj x y :
  Byte.unsigned x = Byte.unsigned y -> byte_eq x y.
Proof.
  destruct x as [x rx]; destruct y as [y ry];
    rewrite /byte_eq /Byte.eq /= => Hxy.
  by case: (Coqlib.zeq x y).
Qed.

Lemma int_unsigned_inj x y :
  Int.unsigned x = Int.unsigned y -> int_eq x y.
Proof.
  destruct x as [x rx]; destruct y as [y ry];
    rewrite /int_eq /Int.eq /= => Hxy.
  by case: (Coqlib.zeq x y).
Qed.

Lemma int64_unsigned_inj x y :
  Int64.unsigned x = Int64.unsigned y -> int64_eq x y.
Proof.
  destruct x as [x rx]; destruct y as [y ry];
    rewrite /int64_eq /Int64.eq /= => Hxy.
  by case: (Coqlib.zeq x y).
Qed.

Module ByteOrderMinimal <: SsrOrderedTypeMinimal.

  Definition t : eqType := byte_eqType.

  Definition eq : t -> t -> bool := fun x y : t => x == y.

  Definition lt : t -> t -> bool := Byte.ltu.

  Hint Unfold eq lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    rewrite /lt /Byte.ltu /Coqlib.zlt /= => x y z.
    case: (Z_lt_dec (Byte.unsigned x) (Byte.unsigned y)) => //=.
    case: (Z_lt_dec (Byte.unsigned y) (Byte.unsigned z)) => //=.
    case: (Z_lt_dec (Byte.unsigned x) (Byte.unsigned z)) => //=.
    move=> Hxz Hyz Hxy _ _.
    apply: False_ind; apply: Hxz.
    exact: (Z.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    rewrite /lt /Byte.ltu /Coqlib.zlt /= => x y.
    case: (Z_lt_dec (Byte.unsigned x) (Byte.unsigned y)) => //=.
    move=> Hlt _.
    apply/negP => Heq.
    rewrite (eqP Heq) in Hlt.
    apply: (Z.lt_irrefl (Byte.unsigned y)).
    assumption.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    case Heq: (x == y); last case Hlt: (lt x y).
    - apply: EQ.
      assumption.
    - exact: (OrderedType.LT Hlt).
    - apply: GT.
      move: Hlt.
      rewrite /lt /Byte.ltu.
      case: (Coqlib.zlt (Byte.unsigned x) (Byte.unsigned y)) => //=.
      move=> Hge _.
      move: (Z.ge_le _ _ Hge) => Hle.
      move: (Z.le_lteq (Byte.unsigned y) (Byte.unsigned x)) => [H _].
      case: (H Hle) => {H} Hyx.
      + by case: (Coqlib.zlt (Byte.unsigned y) (Byte.unsigned x)).
      + apply: False_ind.
        move/negP: Heq; apply.
        rewrite eq_sym.
        exact: (byte_unsigned_inj Hyx).
  Defined.

End ByteOrderMinimal.

Module ByteOrder <: SsrOrderedType := MakeSsrOrderedType ByteOrderMinimal.

Module IntOrderMinimal <: SsrOrderedTypeMinimal.

  Definition t : eqType := int_eqType.

  Definition eq : t -> t -> bool := fun x y : t => x == y.

  Definition lt : t -> t -> bool := Int.ltu.

  Hint Unfold eq lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    rewrite /lt /Int.ltu /Coqlib.zlt /= => x y z.
    case: (Z_lt_dec (Int.unsigned x) (Int.unsigned y)) => //=.
    case: (Z_lt_dec (Int.unsigned y) (Int.unsigned z)) => //=.
    case: (Z_lt_dec (Int.unsigned x) (Int.unsigned z)) => //=.
    move=> Hxz Hyz Hxy _ _.
    apply: False_ind; apply: Hxz.
    exact: (Z.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    rewrite /lt /Int.ltu /Coqlib.zlt /= => x y.
    case: (Z_lt_dec (Int.unsigned x) (Int.unsigned y)) => //=.
    move=> Hlt _.
    apply/negP => Heq.
    rewrite (eqP Heq) in Hlt.
    apply: (Z.lt_irrefl (Int.unsigned y)).
    assumption.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    case Heq: (x == y); last case Hlt: (lt x y).
    - apply: EQ.
      assumption.
    - exact: (OrderedType.LT Hlt).
    - apply: GT.
      move: Hlt.
      rewrite /lt /Int.ltu.
      case: (Coqlib.zlt (Int.unsigned x) (Int.unsigned y)) => //=.
      move=> Hge _.
      move: (Z.ge_le _ _ Hge) => Hle.
      move: (Z.le_lteq (Int.unsigned y) (Int.unsigned x)) => [H _].
      case: (H Hle) => {H} Hyx.
      + by case: (Coqlib.zlt (Int.unsigned y) (Int.unsigned x)).
      + apply: False_ind.
        move/negP: Heq; apply.
        rewrite eq_sym.
        exact: (int_unsigned_inj Hyx).
  Defined.

End IntOrderMinimal.

Module IntOrder <: SsrOrderedType := MakeSsrOrderedType IntOrderMinimal.

Module Int64OrderMinimal <: SsrOrderedTypeMinimal.

  Definition t : eqType := int64_eqType.

  Definition eq : t -> t -> bool := fun x y : t => x == y.

  Definition lt : t -> t -> bool := Int64.ltu.

  Hint Unfold eq lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    rewrite /lt /Int64.ltu /Coqlib.zlt /= => x y z.
    case: (Z_lt_dec (Int64.unsigned x) (Int64.unsigned y)) => //=.
    case: (Z_lt_dec (Int64.unsigned y) (Int64.unsigned z)) => //=.
    case: (Z_lt_dec (Int64.unsigned x) (Int64.unsigned z)) => //=.
    move=> Hxz Hyz Hxy _ _.
    apply: False_ind; apply: Hxz.
    exact: (Z.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    rewrite /lt /Int64.ltu /Coqlib.zlt /= => x y.
    case: (Z_lt_dec (Int64.unsigned x) (Int64.unsigned y)) => //=.
    move=> Hlt _.
    apply/negP => Heq.
    rewrite (eqP Heq) in Hlt.
    apply: (Z.lt_irrefl (Int64.unsigned y)).
    assumption.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> x y.
    case Heq: (x == y); last case Hlt: (lt x y).
    - apply: EQ.
      assumption.
    - exact: (OrderedType.LT Hlt).
    - apply: GT.
      move: Hlt.
      rewrite /lt /Int64.ltu.
      case: (Coqlib.zlt (Int64.unsigned x) (Int64.unsigned y)) => //=.
      move=> Hge _.
      move: (Z.ge_le _ _ Hge) => Hle.
      move: (Z.le_lteq (Int64.unsigned y) (Int64.unsigned x)) => [H _].
      case: (H Hle) => {H} Hyx.
      + by case: (Coqlib.zlt (Int64.unsigned y) (Int64.unsigned x)).
      + apply: False_ind.
        move/negP: Heq; apply.
        rewrite eq_sym.
        exact: (int64_unsigned_inj Hyx).
  Defined.

End Int64OrderMinimal.

Module Int64Order <: SsrOrderedType := MakeSsrOrderedType Int64OrderMinimal.



(** Additional functions added to CompCert modules Byte, Int, and Int64 *)

Module Byte.
  Include CompCert.Integers.Byte.
  Definition pow_pos x := Pos.iter (Byte.mul x) Byte.one.
  Definition of_bool b := if b then Byte.one else Byte.zero.
  Definition to_bool n := if n == zero then false else true.
  Lemma to_boolK : forall b : bool, to_bool (of_bool b) = b.
  Proof.
    by case.
  Qed.
  Lemma of_boolK1 : forall n : byte, n = zero -> of_bool (to_bool n) = zero.
  Proof.
    move=> n H; rewrite H.
    reflexivity.
  Qed.
  Lemma of_boolK2 : forall n : byte, n <> zero -> of_bool (to_bool n) = one.
  Proof.
    move=> n H.
    rewrite /of_bool /to_bool.
    move/eqP/negPf: H => H.
    by rewrite H.
  Qed.
End Byte.

Module Int.
  Include CompCert.Integers.Int.
  Definition pow_pos x := Pos.iter (Int.mul x) Int.one.
  Definition of_bool b := if b then Int.one else Int.zero.
  Definition to_bool n := if n == zero then false else true.
  Lemma to_boolK : forall b : bool, to_bool (of_bool b) = b.
  Proof.
    by case.
  Qed.
  Lemma of_boolK1 : forall n : int, n = zero -> of_bool (to_bool n) = zero.
  Proof.
    move=> n H; rewrite H.
    reflexivity.
  Qed.
  Lemma of_boolK2 : forall n : int, n <> zero -> of_bool (to_bool n) = one.
  Proof.
    move=> n H.
    rewrite /of_bool /to_bool.
    move/eqP/negPf: H => H.
    by rewrite H.
  Qed.
End Int.

Module Int64.
  Include CompCert.Integers.Int64.
  Definition int64_pow_pos x := Pos.iter (Int64.mul x) Int64.one.
  Definition of_bool b := if b then Int64.one else Int64.zero.
  Definition to_bool n := if n == zero then false else true.
  Lemma to_boolK : forall b : bool, to_bool (of_bool b) = b.
  Proof.
    by case.
  Qed.
  Lemma of_boolK1 : forall n : int64, n = zero -> of_bool (to_bool n) = zero.
  Proof.
    move=> n H; rewrite H.
    reflexivity.
  Qed.
  Lemma of_boolK2 : forall n : int64, n <> zero -> of_bool (to_bool n) = one.
  Proof.
    move=> n H.
    rewrite /of_bool /to_bool.
    move/eqP/negPf: H => H.
    by rewrite H.
  Qed.
End Int64.

Strategy 0 [Wordsize_32.wordsize].
Notation int := Int.int.

Strategy 0 [Wordsize_8.wordsize].
Notation byte := Byte.int.

Strategy 0 [Wordsize_64.wordsize].
Notation int64 := Int64.int.

Global Opaque Int.repr Int64.repr Byte.repr.
