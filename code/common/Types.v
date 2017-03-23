
From Coq Require Import OrderedType FMaps FSets ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Structure with a base type t. *)

Module NatType <: Equalities.Typ.
  Definition t : Set := nat.
End NatType.

Module IntType <: Equalities.Typ.
  Definition t : Set := int.
End IntType.

Module PosType <: Equalities.Typ.
  Definition t : Set := positive.
End PosType.

Module NType <: Equalities.Typ.
  Definition t : Set := N.
End NType.

Module ZType <: Equalities.Typ.
  Definition t : Set := Z.
End ZType.



(** Structure with a base eqType t. *)

Module Type EQTYPE.
  Parameter t : eqType.
End EQTYPE.

Module IntEqtype <: EQTYPE.
  Definition t := int_eqType.
End IntEqtype.



(** Structure with a base type t equipped with a reflectable Boolean equality. *)

Module Type HAS_REFLECTABLE_EQB (Import X : Equalities.Typ).
  Parameter Inline eqb : t -> t -> bool.
  Parameter Inline eqb_refl : forall x : t, eqb x x.
  Parameter Inline eqb_eq : forall x y : t, eqb x y -> x = y.
End HAS_REFLECTABLE_EQB.

Module Type REFLECTABLE := Equalities.Typ <+ HAS_REFLECTABLE_EQB.

Module MakeReflection (X : REFLECTABLE).

  Lemma eqbP : Equality.axiom X.eqb.
  Proof.
    move=> x y.
    case H: (X.eqb x y).
    - apply: ReflectT.
      apply: X.eqb_eq.
      assumption.
    - apply: ReflectF.
      move/idP/eqP/eqP: H => Hne Heq; apply: Hne.
      rewrite Heq.
      exact: X.eqb_refl.
  Qed.

  Canonical reflectable_Mixin := EqMixin eqbP.
  Canonical reflectable_eqType := Eval hnf in EqType X.t reflectable_Mixin.

End MakeReflection.



(** Make (option t) an eqType given that t is an eqType. *)

Module MakeOptionReflectable (X : EQTYPE).

  Definition option_eqb (x y : option X.t) : bool :=
    match x, y with
    | None, None => true
    | None, Some _ => false
    | Some _, None => false
    | Some a, Some b => a == b
    end.

  Lemma option_eqbP : Equality.axiom option_eqb.
  Proof.
    move=> x y; case: y; case: x => /=.
    - move=> x y.
      case H: (x == y).
      + apply: ReflectT.
        rewrite (eqP H).
        reflexivity.
      + apply: ReflectF.
        move=> Heq.
        move/idP/eqP/eqP: H; apply.
        case: Heq => Heq; rewrite Heq.
        exact: eqxx.
    - move=> y.
      apply: ReflectF.
      move=> H; discriminate.
    - move=> x.
      apply: ReflectF.
      move=> H; discriminate.
    - apply: ReflectT.
      reflexivity.
  Qed.

  Canonical option_Mixin := EqMixin option_eqbP.
  Canonical option_eqType := Eval hnf in EqType (option X.t) option_Mixin.

End MakeOptionReflectable.

Module OptionIntEqtype <: EQTYPE.
  Module OptionInt := MakeOptionReflectable(IntEqtype).
  Definition t := OptionInt.option_eqType.
End OptionIntEqtype.



(** Coq OrderedType with Boolean equality. *)

Module Type SsrOrderedTypeMinimal.
  Parameter t : eqType.
  Definition eq : t -> t -> bool := fun x y => x == y.
  Parameter lt : t -> t -> bool.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> x != y.
  Parameter compare : forall x y : t, Compare lt eq x y.
End SsrOrderedTypeMinimal.

Module Type SsrOrderedType <: OrderedType.
  Parameter T : eqType.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := fun x y => x == y.
  Parameter Inline ltb : t -> t -> bool.
  Definition lt : t -> t -> Prop := fun x y => ltb x y.
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End SsrOrderedType.

Module MakeSsrOrderedType (M : SsrOrderedTypeMinimal) <: SsrOrderedType.
  Definition T : eqType := M.t.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := fun x y => x == y.
  Definition ltb : t -> t -> bool := M.lt.
  Definition lt : t -> t -> Prop := fun x y => ltb x y.
  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    exact: eqxx.
  Qed.
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    move=> x y H.
    rewrite /eq eq_sym.
    exact: H.
  Qed.
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    move=> x y z Hxy Hyz.
    rewrite (eqP Hxy).
    exact: Hyz.
  Qed.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z :=
    M.lt_trans.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    move=> x y Hlt Heq.
    move/negP: (M.lt_not_eq Hlt).
    apply.
    assumption.
  Qed.
  Definition compare : forall x y : t, Compare lt eq x y := M.compare.
  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    move=> x y.
    case Hxy: (x == y).
    - left; exact: Hxy.
    - right; move=> Heq.
      apply/negPf: Hxy.
      exact: Heq.
  Qed.
End MakeSsrOrderedType.

Module MakePairEqType (O1 O2 : EQTYPE).
  Definition t : Type := (O1.t * O2.t).
  Definition eq : t -> t -> bool :=
    fun x y => (fst x == fst y) && (snd x == snd y).
  Lemma eqP : Equality.axiom eq.
  Proof.
    move=> [] x1 x2 [] y1 y2.
    rewrite /eq /=.
    case H1: (x1 == y1); case H2: (x2 == y2).
    - apply: ReflectT.
      rewrite (eqP H1) (eqP H2).
      reflexivity.
    - apply: ReflectF => H.
      case: H => H1' H2'.
      apply/negPf: H2.
      rewrite H2'.
      exact: eqxx.
    - apply: ReflectF => H.
      case: H => H1' H2'.
      apply/negPf: H1.
      rewrite H1'.
      exact: eqxx.
    - apply: ReflectF => H.
      case: H => H1' H2'.
      apply/negPf: H1.
      rewrite H1'.
      exact: eqxx.
  Qed.
  Definition pair_eqMixin := EqMixin eqP.
  Canonical pair_eqType := Eval hnf in EqType t pair_eqMixin.
End MakePairEqType.

Module MakeSsrPairOrderedTypeMinimal (O1 O2 : SsrOrderedType) <: SsrOrderedTypeMinimal.

  Module E1 <: EQTYPE.
    Definition t : eqType := O1.T.
  End E1.

  Module E2 <: EQTYPE.
    Definition t : eqType := O2.T.
  End E2.

  Module P := MakePairEqType E1 E2.

  Definition t : eqType := P.pair_eqType.

  Definition eq : t -> t -> bool := fun x y => x == y.

  Definition lt : t -> t -> bool :=
    fun x y =>
      if O1.ltb (fst x) (fst y) then true
      else if (fst x) == (fst y) then O2.ltb (snd x) (snd y)
           else false.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> [] x1 x2 [] y1 y2 [] z1 z2.
    rewrite /lt /=.
    case Hx1y1: (O1.ltb x1 y1).
    - case Hy1z1: (O1.ltb y1 z1).
      + case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        move: (O1.lt_trans Hx1y1 Hy1z1) => Hx1z1'.
        rewrite /O1.lt Hx1z1 in Hx1z1'.
        done.
      + case Ey1z1: (y1 == z1); [idtac | done].
        case Hy2z2: (O2.ltb y2 z2); [idtac | done].
        case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        case Ex1z1: (x1 == z1).
        * rewrite (eqP Ex1z1) -(eqP Ey1z1) in Hx1y1.
          apply: False_ind.
          apply: (O1.lt_not_eq Hx1y1).
          exact: O1.eq_refl.
        * rewrite (eqP Ey1z1) in Hx1y1.
          rewrite Hx1y1 in Hx1z1.
          discriminate.
    - case Ex1y1: (x1 == y1); [idtac | done].
      case Hx2y2: (O2.ltb x2 y2); [idtac | done].
      case Hy1z1: (O1.ltb y1 z1).
      + case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        rewrite (eqP Ex1y1) Hy1z1 in Hx1z1.
        discriminate.
      + case Ey1z1: (y1 == z1); [idtac | done].
        case Hy2z2: (O2.ltb y2 z2); [idtac | done].
        case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        case Ex1z1: (x1 == z1).
        * move=> _ _; exact: (O2.lt_trans Hx2y2 Hy2z2).
        * move: (O1.eq_trans Ex1y1 Ey1z1).
          rewrite /O1.eq Ex1z1.
          done.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x != y.
  Proof.
    move=> [] x1 x2 [] y1 y2.
    rewrite /lt /=.
    case Hx1y1: (O1.ltb x1 y1).
    - move=> _.
      apply/eqP => H.
      case: H => H1 _.
      apply: (O1.lt_not_eq Hx1y1).
      by apply/eqP.
    - case Ex1y1: (x1 == y1); [idtac | done].
      case Hx2y2: (O2.ltb x2 y2); [idtac | done].
      move=> _.
      apply/eqP => H.
      case: H => _ H2.
      apply: (O2.lt_not_eq Hx2y2).
      by apply/eqP.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> [] x1 x2 [] y1 y2.
    move: (O1.compare x1 y1) (O2.compare x2 y2) => Hc1 Hc2.
    inversion_clear Hc1.
    - apply: LT.
      rewrite /lt /=.
      rewrite /O1.lt in H.
      by rewrite H.
    - inversion_clear Hc2.
      + apply: LT.
        rewrite /lt /=.
        case Hx1y1: (O1.ltb x1 y1); [done | idtac].
        rewrite H.
        exact: H0.
      + apply: EQ.
        rewrite /eq /=.
        by apply/andP; split; assumption.
      + apply: GT.
        rewrite /lt /=.
        case Hy1x1: (O1.ltb y1 x1); [done | idtac].
        rewrite (O1.eq_sym H).
        exact: H0.
    - apply: GT.
      rewrite /lt /=.
      by rewrite H.
  Defined.

End MakeSsrPairOrderedTypeMinimal.

Module MakeSsrPairOrderedType (O1 O2 : SsrOrderedType) <: SsrOrderedType.
  Module M := MakeSsrPairOrderedTypeMinimal O1 O2.
  Module P := MakeSsrOrderedType M.
  Include P.
End MakeSsrPairOrderedType.

Module SsrPairOrderedType (O1 O2 : SsrOrderedType) <: SsrOrderedType.

  Module E1 <: EQTYPE.
    Definition t : eqType := O1.T.
  End E1.

  Module E2 <: EQTYPE.
    Definition t : eqType := O2.T.
  End E2.

  Module P := MakePairEqType E1 E2.

  Definition T : eqType := P.pair_eqType.

  Definition t : Type := T.

  Definition eq : t -> t -> Prop :=
    fun x y => x == y.

  Definition ltb : T -> T -> bool :=
    fun x y =>
      if O1.ltb (fst x) (fst y) then true
      else if (fst x) == (fst y) then O2.ltb (snd x) (snd y)
           else false.

  Definition lt : t -> t -> Prop := fun x y => ltb x y.

  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    exact: eqxx.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    move=> x y H.
    rewrite /eq eq_sym.
    exact: H.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    move=> x y z Hxy Hyz.
    rewrite (eqP Hxy).
    exact: Hyz.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> [] x1 x2 [] y1 y2 [] z1 z2.
    rewrite /lt /ltb /=.
    case Hx1y1: (O1.ltb x1 y1).
    - case Hy1z1: (O1.ltb y1 z1).
      + case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        move: (O1.lt_trans Hx1y1 Hy1z1) => Hx1z1'.
        rewrite /O1.lt Hx1z1 in Hx1z1'.
        done.
      + case Ey1z1: (y1 == z1); [idtac | done].
        case Hy2z2: (O2.ltb y2 z2); [idtac | done].
        case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        case Ex1z1: (x1 == z1).
        * rewrite (eqP Ex1z1) -(eqP Ey1z1) in Hx1y1.
          apply: False_ind.
          apply: (O1.lt_not_eq Hx1y1).
          exact: O1.eq_refl.
        * rewrite (eqP Ey1z1) in Hx1y1.
          rewrite Hx1y1 in Hx1z1.
          discriminate.
    - case Ex1y1: (x1 == y1); [idtac | done].
      case Hx2y2: (O2.ltb x2 y2); [idtac | done].
      case Hy1z1: (O1.ltb y1 z1).
      + case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        rewrite (eqP Ex1y1) Hy1z1 in Hx1z1.
        discriminate.
      + case Ey1z1: (y1 == z1); [idtac | done].
        case Hy2z2: (O2.ltb y2 z2); [idtac | done].
        case Hx1z1: (O1.ltb x1 z1); [done | idtac].
        case Ex1z1: (x1 == z1).
        * move=> _ _; exact: (O2.lt_trans Hx2y2 Hy2z2).
        * move: (O1.eq_trans Ex1y1 Ey1z1).
          rewrite /O1.eq Ex1z1.
          done.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    move=> [] x1 x2 [] y1 y2.
    rewrite /lt /ltb /eq /=.
    case Hx1y1: (O1.ltb x1 y1).
    - move=> _ H.
      move/andP: H => [Ex1y1 _].
      exact: (O1.lt_not_eq Hx1y1 Ex1y1).
    - case Ex1y1: (x1 == y1); [idtac | done].
      case Hx2y2: (O2.ltb x2 y2); [idtac | done].
      move=> _ H.
      move/andP: H => [_ Ex2y2].
      exact: (O2.lt_not_eq Hx2y2 Ex2y2).
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    move=> [] x1 x2 [] y1 y2.
    move: (O1.compare x1 y1) (O2.compare x2 y2) => Hc1 Hc2.
    inversion_clear Hc1.
    - apply: LT.
      rewrite /lt /ltb /=.
      rewrite /O1.lt in H.
      by rewrite H.
    - inversion_clear Hc2.
      + apply: LT.
        rewrite /lt /ltb /=.
        case Hx1y1: (O1.ltb x1 y1); [done | idtac].
        rewrite H.
        exact: H0.
      + apply: EQ.
        rewrite /eq /=.
        by apply/andP; split; assumption.
      + apply: GT.
        rewrite /lt /ltb /=.
        case Hy1x1: (O1.ltb y1 x1); [done | idtac].
        rewrite (O1.eq_sym H).
        exact: H0.
    - apply: GT.
      rewrite /lt /ltb /=.
      by rewrite H.
  Defined.

  Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    move=> x y.
    case Hxy: (x == y).
    - left; exact: Hxy.
    - right; move=> Heq.
      apply/negPf: Hxy.
      exact: Heq.
  Qed.

End SsrPairOrderedType.