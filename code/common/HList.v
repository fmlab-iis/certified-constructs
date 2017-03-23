
From Coq Require Import Program Program.Tactics Arith List.
From mathcomp Require Import ssreflect ssrnat.
From Common Require Import Lists.

(** * Formalization of heterogeneous lists.

  This formalization is based on the following paper.
  - Paolo Herms, Claude Marché, Benjamin Monate:
    A Certified Multi-prover Verification Condition Generator.
    VSTTE 2012: 2-17
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope hlist_scope with hlist.

Reserved Notation "x '=i' y" (at level 70, no associativity).
Reserved Notation "x '<>i' y" (at level 70, no associativity).
Reserved Notation "x '=v' y" (at level 70, no associativity).
Reserved Notation "x '<>v' y" (at level 70, no associativity).

Section HList.

  Variable S : Type.

  Variable T : S -> Type.

  (* A lidx is an index of a hlist. *)
  Inductive lidx A : list S -> Type :=
  | HI0 E : lidx A (A :: E)
  | HIS B E : lidx A E -> lidx A (B :: E).

  (* Heterogeneous lists. *)
  Inductive hlist : list S -> Type :=
  | Hnil : hlist nil
  | Hcons A E : T A -> hlist E -> hlist (A :: E).

  Definition hnil : hlist [] := Hnil.



  (* Equalities *)

  Local Open Scope hlist_scope.

  Definition xdil E A := lidx A E.

  (** Equality of lidx. *)

  Definition lidx_eq A B E (i : lidx A E) (j : lidx B E) :=
    EqdepFacts.eq_dep S (xdil E) A i B j.

  Notation "x '=i' y" := (lidx_eq x y) (at level 70, no associativity) : hlist_scope.
  Notation "x '<>i' y" := (~ (lidx_eq x y)) (at level 70, no associativity) : hlist_scope.

  (* Given that i : lidx A E, j : lidx B E, and H : lidx_eq i j, produce
   i = j and change B to A. *)
  Ltac lidx_eq_eq H :=
    match goal with
    | i : lidx ?A ?E, j : lidx ?B ?E, H : lidx_eq ?i ?j |- _ =>
      let Hab := fresh in
      let Hab' := fresh in
      let Heq := fresh in
      inversion H as [Hab [Hab' Heq]];
        clear Hab';
        move: i j Heq H;
        rewrite -Hab => {Hab};
        move=> i j Heq H;
        move: (EqdepFacts.eq_sigT_snd Heq);
        rewrite -{1}eq_rect_eq => {Heq}
    | H : lidx_eq ?i ?j |- _ =>
      let Hab := fresh in
      let Heq := fresh in
      inversion H as [Hab Heq];
        clear Hab;
        move: (EqdepFacts.eq_sigT_snd Heq);
        rewrite -{1}eq_rect_eq => {Heq}
    end.

  Lemma lidx_eq_ty_eq A B E (i : lidx A E) (j : lidx B E) :
    i =i j -> A = B.
  Proof.
    move=> H.
    inversion H as [H1 [H2 H3]].
    reflexivity.
  Qed.

  Lemma lidx_eq_eq A E (i j : lidx A E) :
    i =i j -> i = j.
  Proof.
    move=> H.
    lidx_eq_eq H => Heq.
    exact: Heq.
  Qed.

  Lemma eq_lidx_eq A E (i j : lidx A E) :
    i = j -> i =i j.
  Proof.
    move=> Heq; rewrite Heq.
    exact: EqdepFacts.eq_dep_intro.
  Qed.

  Lemma lidx_neq_neq A E (x y : lidx A E) :
    x <>i y -> x <> y.
  Proof.
    move=> Hne Hxy; apply: Hne.
    apply: eq_lidx_eq.
    exact: Hxy.
  Qed.

  Lemma neq_lidx_neq A E (x y : lidx A E) :
    x <> y -> x <>i y.
  Proof.
    move=> Hne Hxy; apply: Hne.
    apply: lidx_eq_eq.
    exact: Hxy.
  Qed.

  Lemma ty_neq_lidx_neq A B E (x : lidx A E) (y : lidx B E) :
    A <> B -> x <>i y.
  Proof.
    move=> Hne Hxy; apply: Hne.
    inversion Hxy.
    reflexivity.
  Qed.

  Lemma lidx_eq_his_eq A B E (x : lidx A E) (y : lidx B E) ty :
    x =i y -> HIS ty x =i HIS ty y.
  Proof.
    move=> Hxy; rewrite Hxy.
    reflexivity.
  Qed.

  Lemma his_eq_lidx_eq A B E (x : lidx A E) (y : lidx B E) ty :
    HIS ty x =i HIS ty y -> x =i y.
  Proof.
    move=> Hxy.
    dependent destruction Hxy.
    reflexivity.
  Qed.

  (** Equality of values. *)

  Definition value_eq A B (x : T A) (y : T B) :=
    EqdepFacts.eq_dep S T A x B y.

  Notation "x '=v' y" := (value_eq x y) (at level 70, no associativity) : hlist_scope.
  Notation "x '<>v' y" := (~ (value_eq x y)) (at level 70, no associativity) : hlist_scope.

  Ltac value_eq_eq H :=
    match goal with
    | i : T ?A, j : T ?B, H : value_eq ?i ?j |- _ =>
      let Hab := fresh in
      let Hab' := fresh in
      let Heq := fresh in
      inversion H as [Hab [Hab' Heq]];
        clear Hab';
        move: i j Heq H;
        rewrite -Hab => {Hab};
        move=> i j Heq H;
        move: (EqdepFacts.eq_sigT_snd Heq);
        rewrite -{1}eq_rect_eq => {Heq}
    | H : value_eq ?i ?j |- _ =>
      let Hab := fresh in
      let Heq := fresh in
      inversion H as [Hab Heq];
        clear Hab;
        move: (EqdepFacts.eq_sigT_snd Heq);
        rewrite -{1}eq_rect_eq => {Heq}
    end.

  Lemma value_eq_ty_eq A B (x : T A) (y : T B) :
    x =v y -> A = B.
  Proof.
    move=> H.
    inversion H as [H1 [H2 H3]].
    reflexivity.
  Qed.

  Lemma value_eq_eq A (x : T A) (y : T A) :
    x =v y -> x = y.
  Proof.
    move=> H.
    value_eq_eq H => Heq.
    exact: Heq.
  Qed.

  Lemma eq_value_eq A (x y : T A) :
    x = y -> x =v y.
  Proof.
    move=> Heq; rewrite Heq.
    exact: EqdepFacts.eq_dep_intro.
  Qed.

  Lemma value_neq_neq A (x y : T A) :
    x <>v y -> x <> y.
  Proof.
    move=> Hne Hxy; apply: Hne.
    apply: eq_value_eq.
    exact: Hxy.
  Qed.

  Lemma neq_value_neq A (x y : T A) :
    x <> y -> x <>v y.
  Proof.
    move=> Hne Hxy; apply: Hne.
    apply: value_eq_eq.
    exact: Hxy.
  Qed.

  Lemma ty_neq_value_neq A B (x : T A) (y : T B) :
    A <> B -> x <>v y.
  Proof.
    move=> Hne Hxy; apply: Hne.
    inversion Hxy.
    reflexivity.
  Qed.



  (** Access and update a heterogeneous list. *)

  (* Access an index of a heterogeneous list. *)
  Program Fixpoint acclidx A E (i : lidx A E) (l : hlist E) : T A :=
    match l with
    | Hnil => !
    | Hcons _ _ h q =>
      match i with
      | HI0 _ => h
      | HIS _ _ i1 => acclidx i1 q
      end
    end.
  Next Obligation.
      by inversion i.
  Qed.

  (* Update an index of a heterogeneous list. *)
  Program Fixpoint updlidx A E (i : lidx A E) (v : T A) (l : hlist E) : hlist E :=
    match l with
    | Hnil => !
    | Hcons _ _ h q =>
      match i with
      | HI0 _ => Hcons v q
      | HIS _ _ i1 => Hcons h (updlidx i1 v q)
      end
    end.
  Next Obligation.
      by inversion i.
  Qed.

  Lemma acclidx_updlidx_heq A B E :
    forall (i : lidx A E) (j : lidx B E) (v : T B) (l : hlist E),
      i =i j ->
      acclidx i (updlidx j v l) =v v.
  Proof.
    move=> i j v l Heq.
    rewrite Heq => {A i Heq}.
    elim: l B j v => {E}.
    - move=> A i v.
      by inversion i.
    - move=> A E va l Hind B i vb.
      move: va vb.
      dependent destruction i => /=.
      + move=> _ vb.
        exact: EqdepFacts.eq_dep_intro.
      + move=> _ vb.
        exact: (Hind B i vb).
  Qed.

  Lemma acclidx_updlidx_eq A E :
    forall (i : lidx A E) (j : lidx A E) (v : T A) (l : hlist E),
      i = j ->
      acclidx i (updlidx j v l) = v.
  Proof.
    move=> i j v l Heq.
    move: (eq_lidx_eq Heq) => {Heq} Heq.
    move: (acclidx_updlidx_heq v l Heq) => Hveq.
    value_eq_eq Hveq => {Hveq} Hveq.
    exact: Hveq.
  Qed.

  Lemma acclidx_updlidx_hneq A B E :
    forall (i : lidx A E) (j : lidx B E) (v : T B) (l : hlist E),
      i <>i j ->
      acclidx i (updlidx j v l) = acclidx i l.
  Proof.
    move=> i j v l Hne.
    elim: l A B i j Hne v => {E}.
    - move=> A B i j Hne v.
      by inversion i.
    - move=> A E va l Hind A' B i j Hne vb.
      dependent destruction j => /=.
      + dependent destruction i => /=.
        * apply: False_ind.
          apply: Hne.
          reflexivity.
        * reflexivity.
      + dependent destruction i => /=.
        * reflexivity.
        * apply: Hind => Heq.
          apply: Hne.
          rewrite Heq.
          reflexivity.
  Qed.

  Lemma acclidx_updlidx_neq A E :
    forall (i : lidx A E) (j : lidx A E) (v : T A) (l : hlist E),
      i <> j ->
      acclidx i (updlidx j v l) = acclidx i l.
  Proof.
    move=> i j v l Hne.
    move: (neq_lidx_neq Hne) => {Hne} Hne.
    apply: acclidx_updlidx_hneq.
    exact: Hne.
  Qed.

  Lemma acclidx_updlidx_ty_neq A B E :
    forall (i : lidx A E) (j : lidx B E) (v : T B) (l : hlist E),
      A <> B ->
      acclidx i (updlidx j v l) = acclidx i l.
  Proof.
    move=> i j v l Hne.
    apply: acclidx_updlidx_hneq.
    apply: ty_neq_lidx_neq.
    exact: Hne.
  Qed.

  (** Other operations *)

  Fixpoint length E (l : hlist E) : nat :=
    match l with
    | Hnil => 0
    | Hcons _ _ hd tl => (length tl).+1
    end.

  Program Definition hd (E : nonempty_list S) (l : hlist E) : T (nonempty_hd E) :=
    match l with
    | Hnil => !
    | Hcons _ _ hd _ => hd
    end.
  Next Obligation.
    move: Heq_anonymous => {l Heq_l}.
    elim: E.
    discriminate.
  Qed.
  Next Obligation.
    move=> {l wildcard'1 Heq_l hd}.
    move: wildcard' wildcard'0 Heq_anonymous.
    elim: E => /=.
    move=> hd tl hd' tl' [] Hhd _.
    assumption.
  Qed.

  Definition tl E (l : hlist E) : hlist (List.tl E) :=
    match l with
    | Hnil => Hnil
    | Hcons _ _ _ tl => tl
    end.

End HList.

Notation "x '=i' y" := (lidx_eq x y) (at level 70, no associativity) : hlist_scope.
Notation "x '<>i' y" := (~ (lidx_eq x y)) (at level 70, no associativity) : hlist_scope.
Notation "x '=v' y" := (value_eq x y) (at level 70, no associativity) : hlist_scope.
Notation "x '<>v' y" := (~ (value_eq x y)) (at level 70, no associativity) : hlist_scope.
