
(** * Stores of variable values *)

From Coq Require Import Program Program.Tactics FMaps ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Common Require Import Types HList FMaps ZAriths Env Var.
Import HEnv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Stores as total maps from variables to values of a single type. *)

Module Type TSTORE.

  Section TStore.

    Variable value : Type.

    Parameter var : eqType.

    Parameter t : Type -> Type.

    Parameter acc : var -> t value -> value.

    Parameter upd : var -> value -> t value -> t value.

    Parameter acc_upd_eq :
      forall x y v s,
        x == y ->
        acc x (upd y v s) = v.

    Parameter acc_upd_neq :
      forall x y v s,
        x != y ->
        acc x (upd y v s) = acc x s.

    Parameter Upd : var -> value -> t value -> t value -> Prop.

    Parameter Upd_upd :
      forall x v s,
        Upd x v s (upd x v s).

    Parameter acc_Upd_eq :
      forall x y v s1 s2,
        x == y ->
        Upd y v s1 s2 ->
        acc x s2 = v.

    Parameter acc_Upd_neq :
      forall x y v s1 s2,
        x != y ->
        Upd y v s1 s2 ->
        acc x s2 = acc x s1.

    End TStore.

End TSTORE.

Module MakeTStore (X : SsrOrderedType) <: TSTORE.

  Section TStore.

    Variable value : Type.

    Definition var := X.T.

    Definition t : Type := var -> value.

    Parameter empty : var -> value.

    Definition acc (x : var) (s : t) := s x.

    Definition upd (x : var) (v : value) (s : t) :=
      fun (y : var) => if y == x then v else acc y s.

    Lemma acc_upd_eq x y v s :
      x == y ->
      acc x (upd y v s) = v.
    Proof.
      rewrite /acc /upd => Hxy.
      rewrite Hxy.
      reflexivity.
    Qed.

    Lemma acc_upd_neq x y v s :
      x != y ->
      acc x (upd y v s) = acc x s.
    Proof.
      rewrite {1}/acc /upd => Hxy.
      rewrite (negPf Hxy).
      reflexivity.
    Qed.

    Definition Upd x v (s1 s2 : t) : Prop :=
      forall y, acc y s2 = acc y (upd x v s1).

    Lemma Upd_upd :
      forall x v s,
        Upd x v s (upd x v s).
    Proof.
      move=> x v s y.
      reflexivity.
    Qed.

    Lemma acc_Upd_eq :
      forall x y v s1 s2,
        x == y ->
        Upd y v s1 s2 ->
        acc x s2 = v.
    Proof.
      move=> x y v s1 s2 Hxy Hupd.
      move: (Hupd x) => Hx.
      rewrite (acc_upd_eq _ _ Hxy) in Hx.
      assumption.
    Qed.

    Lemma acc_Upd_neq :
      forall x y v s1 s2,
        x != y ->
        Upd y v s1 s2 ->
        acc x s2 = acc x s1.
    Proof.
      move=> x y v s1 s2 Hxy Hupd.
      move: (Hupd x) => Hx.
      rewrite (acc_upd_neq _ _ Hxy) in Hx.
      assumption.
    Qed.

  End TStore.

End MakeTStore.

Module TStoreAdapter (X : SsrOrderedType) (V : Equalities.Typ).
  Module S := MakeTStore X.
  Definition value := V.t.
  Definition var := S.var.
  Definition t := S.t value.
  Definition acc x (s : t) := S.acc x s.
  Definition upd x v (s : t) := S.upd x v s.
  Lemma acc_upd_eq :
    forall x y v (s : t),
      x == y ->
      acc x (upd y v s) = v.
  Proof.
    move=> x y v s.
    exact: S.acc_upd_eq.
  Qed.
  Lemma acc_upd_neq :
    forall x y v (s : t),
      x != y ->
      acc x (upd y v s) = acc x s.
  Proof.
    move=> x y v s.
    exact: S.acc_upd_neq.
  Qed.
  Definition Upd x v (s1 s2 : t) := S.Upd x v s1 s2.
  Lemma Upd_upd :
    forall x v s,
      Upd x v s (upd x v s).
  Proof.
    move=> x v s y.
    exact: S.Upd_upd.
  Qed.
  Lemma acc_Upd_eq :
    forall x y v s1 s2,
      x == y ->
      Upd y v s1 s2 ->
      acc x s2 = v.
  Proof.
    move=> x y v s1 s2.
    exact: S.acc_Upd_eq.
  Qed.
  Lemma acc_Upd_neq :
    forall x y v s1 s2,
      x != y ->
      Upd y v s1 s2 ->
      acc x s2 = acc x s1.
  Proof.
    move=> x y v s1 s2.
    exact: S.acc_Upd_neq.
  Qed.
End TStoreAdapter.



(** Stores as partial maps from variables to values of a single type. *)

Module Type PSTORE.

  Section PStore.

    Variable value : Type.

    Parameter var : eqType.

    Parameter t : Type -> Type.

    Parameter empty : t value.

    Parameter acc : var -> t value -> option value.

    Parameter upd : var -> value -> t value -> t value.

    Parameter unset : var -> t value -> t value.

    Parameter acc_upd_eq :
      forall x y v s,
        x == y ->
        acc x (upd y v s) = Some v.

    Parameter acc_upd_neq :
      forall x y v s,
        x != y ->
        acc x (upd y v s) = acc x s.

    Parameter acc_empty :
      forall x, acc x empty = None.

    Parameter acc_unset_eq :
      forall x y s,
        x == y ->
        acc x (unset y s) = None.

    Parameter acc_unset_neq :
      forall x y s,
        x != y ->
        acc x (unset y s) = acc x s.

    Parameter Empty : t value -> Prop.

    Parameter Upd : var -> value -> t value -> t value -> Prop.

    Parameter Unset : var -> t value -> t value -> Prop.

    Parameter Empty_acc :
      forall x s,
        Empty s ->
        acc x s = None.

    Parameter Upd_upd :
      forall x v s,
        Upd x v s (upd x v s).

    Parameter Unset_unset :
      forall x s,
        Unset x s (unset x s).

    Parameter acc_Upd_eq :
      forall x y v s1 s2,
        x == y ->
        Upd y v s1 s2 ->
        acc x s2 = Some v.

    Parameter acc_Upd_neq :
      forall x y v s1 s2,
        x != y ->
        Upd y v s1 s2 ->
        acc x s2 = acc x s1.

    Parameter acc_Unset_eq :
      forall x y s1 s2,
        x == y ->
        Unset y s1 s2 ->
        acc x s2 = None.

    Parameter acc_Unset_neq :
      forall x y s1 s2,
        x != y ->
        Unset y s1 s2 ->
        acc x s2 = acc x s1.

  End PStore.

End PSTORE.

Module MakePStore (X : SsrOrderedType) <: PSTORE.

  Module M := FMapList.Make(X).
  Module L := FMapLemmas(M).

  Section PStore.

    Definition var : eqType := X.T.

    Variable value : Type.

    Definition t : Type := M.t value.

    Definition empty : t := M.empty value.

    Definition acc (x : var) (s : t) := M.find x s.

    Definition upd (x : var) (v : value) (s : t) := M.add x v s.

    Definition unset (x : var) (s : t) := M.remove x s.

    Lemma acc_upd_eq x y v s :
      x == y ->
      acc x (upd y v s) = Some v.
    Proof.
      rewrite /acc /upd => Hxy.
      rewrite (eqP Hxy) => {Hxy x}.
      apply: L.find_add_eq.
      reflexivity.
    Qed.

    Lemma acc_upd_neq x y v s :
      x != y ->
      acc x (upd y v s) = acc x s.
    Proof.
      rewrite /acc /upd => Hxy.
      apply: L.find_add_neq.
      exact: (negP Hxy).
    Qed.

    Lemma acc_empty :
      forall x, acc x empty = None.
    Proof.
      exact: L.empty_o.
    Qed.

    Lemma acc_unset_eq :
      forall x y s,
        x == y ->
        acc x (unset y s) = None.
    Proof.
      move=> x y s Heq.
      apply: L.remove_eq_o.
      rewrite eq_sym.
      exact: Heq.
    Qed.

    Lemma acc_unset_neq :
      forall x y s,
        x != y ->
        acc x (unset y s) = acc x s.
    Proof.
      move=> x y s Hne.
      apply: L.remove_neq_o.
      move=> Heq.
      move/eqP: Hne; apply.
      by rewrite (eqP Heq).
    Qed.

    Definition Empty (s : t) : Prop := M.Empty s.

    Definition Upd x v s1 s2 : Prop :=
      forall y, acc y s2 = acc y (upd x v s1).

    Definition Unset x s1 s2 : Prop :=
      forall y, acc y s2 = acc y (unset x s1).

    Lemma Empty_acc :
      forall x s,
        Empty s ->
        acc x s = None.
    Proof.
      move=> x s Hemp.
      exact: (L.Empty_find _ Hemp).
    Qed.

    Lemma Upd_upd :
      forall x v s,
        Upd x v s (upd x v s).
    Proof.
      move=> x v s y.
      reflexivity.
    Qed.

    Lemma Unset_unset :
      forall x s,
        Unset x s (unset x s).
    Proof.
      move=> x s y.
      reflexivity.
    Qed.

    Lemma acc_Upd_eq :
      forall x y v s1 s2,
        x == y ->
        Upd y v s1 s2 ->
        acc x s2 = Some v.
    Proof.
      move=> x y v s1 s2 Hxy Hupd.
      move: (Hupd x).
      rewrite (acc_upd_eq _ _ Hxy).
      by apply.
    Qed.

    Lemma acc_Upd_neq :
      forall x y v s1 s2,
        x != y ->
        Upd y v s1 s2 ->
        acc x s2 = acc x s1.
    Proof.
      move=> x y v s1 s2 Hxy Hupd.
      move: (Hupd x).
      rewrite (acc_upd_neq _ _ Hxy).
      by apply.
    Qed.

    Lemma acc_Unset_eq :
      forall x y s1 s2,
        x == y ->
        Unset y s1 s2 ->
        acc x s2 = None.
    Proof.
      move=> x y s1 s2 Hxy Hunset.
      move: (Hunset x).
      rewrite (acc_unset_eq _ Hxy).
      by apply.
    Qed.

    Lemma acc_Unset_neq :
      forall x y s1 s2,
        x != y ->
        Unset y s1 s2 ->
        acc x s2 = acc x s1.
    Proof.
      move=> x y s1 s2 Hxy Hunset.
      move: (Hunset x).
      rewrite (acc_unset_neq _ Hxy).
      by apply.
    Qed.

  End PStore.

End MakePStore.

Module PStoreAdapter (X : SsrOrderedType) (V : Equalities.Typ).
  Module S := MakePStore X.
  Definition var := S.var.
  Definition value := V.t.
  Definition t := S.t value.
  Definition empty := S.empty value.
  Definition acc x (s : t) := S.acc x s.
  Definition upd x v (s : t) := S.upd x v s.
  Definition unset x (s : t) := S.unset x s.
  Lemma acc_upd_eq :
    forall x y v s,
      x == y ->
      acc x (upd y v s) = Some v.
  Proof.
    move=> x y v s.
    exact: S.acc_upd_eq.
  Qed.
  Lemma acc_upd_neq :
    forall x y v s,
      x != y ->
      acc x (upd y v s) = acc x s.
  Proof.
    move=> x y v s.
    exact: S.acc_upd_neq.
  Qed.
  Lemma acc_empty :
    forall x, acc x empty = None.
  Proof.
    exact: S.acc_empty.
  Qed.
  Lemma acc_unset_eq :
    forall x y s,
      x == y ->
      acc x (unset y s) = None.
  Proof.
    exact: S.acc_unset_eq.
  Qed.
  Lemma acc_unset_neq :
    forall x y s,
      x != y ->
      acc x (unset y s) = acc x s.
  Proof.
    exact: S.acc_unset_neq.
  Qed.
  Definition Empty (s : t) : Prop := S.Empty s.
  Definition Upd x v (s1 s2 : t) : Prop := S.Upd x v s1 s2.
  Definition Unset x (s1 s2 : t) : Prop := S.Unset x s1 s2.
  Lemma Empty_acc :
    forall x s,
      Empty s ->
      acc x s = None.
  Proof.
    exact: S.Empty_acc.
  Qed.
  Lemma Upd_upd :
    forall x v s,
      Upd x v s (upd x v s).
  Proof.
    exact: S.Upd_upd.
  Qed.
  Lemma Unset_unset :
    forall x s,
      Unset x s (unset x s).
  Proof.
    exact: S.Unset_unset.
  Qed.
  Lemma acc_Upd_eq :
    forall x y v s1 s2,
      x == y ->
      Upd y v s1 s2 ->
      acc x s2 = Some v.
  Proof.
    exact: S.acc_Upd_eq.
  Qed.
  Lemma acc_Upd_neq :
    forall x y v s1 s2,
      x != y ->
      Upd y v s1 s2 ->
      acc x s2 = acc x s1.
  Proof.
    exact: S.acc_Upd_neq.
  Qed.
  Lemma acc_Unset_eq :
    forall x y s1 s2,
      x == y ->
      Unset y s1 s2 ->
      acc x s2 = None.
  Proof.
    exact: S.acc_Unset_eq.
  Qed.
  Lemma acc_Unset_neq :
    forall x y s1 s2,
      x != y ->
      Unset y s1 s2 ->
      acc x s2 = acc x s1.
  Proof.
    exact: S.acc_Unset_neq.
  Qed.
End PStoreAdapter.

Module VStore := MakePStore NOrder.



(** Stores with heterogeneous values. *)

Module Type HSTORE.

  Local Open Scope hlist_scope.

  Parameter T : Set.

  Parameter V : T -> Set.

  Parameter t : HEnv.t T -> Type.

  Parameter empty : forall E : HEnv.t T, t E.

  Parameter upd :
    forall (E : HEnv.t T) (ty : T),
      pvar E ty -> V ty -> t E -> t E.

  Parameter acc :
    forall (E : HEnv.t T) (ty : T),
      pvar E ty -> t E -> V ty.

  Parameter bisim : forall (E : HEnv.t T), t E -> t E -> Prop.

  Axiom acc_upd_heq :
    forall (E : HEnv.t T) (tyx tyy : T) (x : pvar E tyx) (y : pvar E tyy)
           (e : V tyy) (s : t E),
      pvar_var x == pvar_var y ->
      acc x (upd y e s) =v e.

  Axiom acc_upd_eq :
    forall (E : HEnv.t T) (ty : T) (x : pvar E ty) (y : pvar E ty)
           (e : V ty) (s : t E),
      pvar_var x == pvar_var y ->
      acc x (upd y e s) = e.

  Axiom acc_upd_neq :
    forall (E : HEnv.t T) (tyx tyy : T) (x : pvar E tyx) (y : pvar E tyy)
           (e : V tyy) (s : t E),
      pvar_var x != pvar_var y ->
      acc x (upd y e s) = acc x s.

  Axiom bisim_refl : forall (E : HEnv.t T) (s : t E), bisim s s.

  Axiom bisim_pvar_inv :
    forall (E : HEnv.t T) (s1 s2 : t E) (ty : T) (x : pvar E ty),
      bisim s1 s2 -> acc x s1 = acc x s2.

End HSTORE.

Module Type HETEROGENEOUS.
  Parameter T : Set.
  Parameter V : T -> Set.
  Parameter default : forall (x : T), V x.
End HETEROGENEOUS.

Module MakeHStore (H : HETEROGENEOUS) <: HSTORE.

  Local Open Scope hlist_scope.

  Definition T : Set := H.T.

  Definition V : T -> Set := H.V.

  Definition t (E : HEnv.t T) : Type := hlist V (HEnv.vtypes E).

  Program Fixpoint defaults (types : list T) : hlist V types :=
    match types with
    | nil => hnil V
    | cons hd tl => Hcons (H.default hd) (defaults tl)
    end.

  Definition empty (E : HEnv.t T) : t E := defaults (HEnv.vtypes E).

  Definition upd E ty (x : pvar E ty) (v : V ty) (st : t E) : t E :=
    updlidx (pvar_lidx x) v st.

  Definition acc E ty (x : pvar E ty) (st : t E) : V ty :=
    acclidx (pvar_lidx x) st.

  Definition bisim E (s1 s2 : t E) : Prop :=
    forall ty (x : pvar E ty), acc x s1 = acc x s2.

  Lemma acc_upd_heq E tyx tyy (x : pvar E tyx) (y : pvar E tyy)
        (e : V tyy) (s : t E) :
    pvar_var x == pvar_var y ->
    (acc x (upd y e s) =v e).
  Proof.
    rewrite /acc /upd /= => Hxy.
    rewrite acclidx_updlidx_heq.
    - reflexivity.
    - apply: pvar_lidx_heq.
      assumption.
  Qed.

  Lemma acc_upd_eq E ty (x y : pvar E ty) (e : V ty) (s : t E) :
    pvar_var x == pvar_var y ->
    acc x (upd y e s) = e.
  Proof.
    move=> Hxy.
    apply: value_eq_eq.
    apply: acc_upd_heq.
    assumption.
  Qed.

  Lemma acc_upd_neq E tyx tyy (x : pvar E tyx) (y : pvar E tyy)
        (e : V tyy) (s : t E) :
    pvar_var x != pvar_var y ->
    acc x (upd y e s) = acc x s.
  Proof.
    rewrite /acc /upd /= => Hne.
    rewrite acclidx_updlidx_hneq.
    - reflexivity.
    - apply: pvar_lidx_hneq.
      assumption.
  Qed.

  Lemma bisim_refl E (s : t E) : bisim s s.
  Proof.
    move=> ty x; reflexivity.
  Qed.

  Lemma bisim_pvar_inv E (s1 s2 : t E) ty (x : pvar E ty) :
    bisim s1 s2 -> acc x s1 = acc x s2.
  Proof.
    move=> Hs.
    exact: Hs.
  Qed.

End MakeHStore.
