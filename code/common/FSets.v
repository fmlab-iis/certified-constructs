
(** * Some auxiliary lemmas for FSets. *)

From Coq Require Import FSets OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Common Require Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Module FSetLemmas (S : FSetInterface.S).

  Module F := Facts(S).
  Module OP := OrdProperties(S).
  Include F.
  Include OP.

  Lemma memP x (s : S.t) : reflect (S.In x s) (S.mem x s).
  Proof.
    case H: (S.mem x s).
    - apply: ReflectT.
      exact: (S.mem_2 H).
    - apply: ReflectF.
      move=> Hin; move: (S.mem_1 Hin).
      rewrite H; discriminate.
  Qed.

  Lemma mem_singleton1 :
    forall x y,
      S.mem x (S.singleton y) -> S.E.eq x y.
  Proof.
    move=> x y /memP Hin.
    move: (S.singleton_1 Hin) => Heq.
    exact: (S.E.eq_sym Heq).
  Qed.

  Lemma mem_singleton2 :
    forall x y,
      S.E.eq x y -> S.mem x (S.singleton y).
  Proof.
    move=> x y Heq.
    apply/memP.
    move: (S.E.eq_sym Heq) => {Heq} Heq.
    exact: (S.singleton_2 Heq).
  Qed.

  Lemma not_mem_singleton1 :
    forall x y,
      ~~ S.mem x (S.singleton y) ->
      ~ S.E.eq x y.
  Proof.
    move=> x y /negP Hmem.
    move=> Heq; apply: Hmem.
    apply/memP.
    move: (S.E.eq_sym Heq) => {Heq} Heq.
    exact: (S.singleton_2 Heq).
  Qed.

  Lemma not_mem_singleton2 :
    forall x y,
      ~ S.E.eq x y ->
      ~~ S.mem x (S.singleton y).
  Proof.
    move=> x y Heq.
    apply/negP => Hmem; apply: Heq.
    exact: mem_singleton1.
  Qed.

  Lemma mem_add1 :
    forall x y s,
      S.mem x (S.add y s) ->
      S.E.eq x y \/ S.mem x s.
  Proof.
    move=> x y s /memP Hin.
    move: (F.add_iff s y x) => [H _].
    move: (H Hin); case => {Hin H}.
    - move=> Heq; left.
      exact: S.E.eq_sym.
    - move=> Hin; right.
      apply/memP; assumption.
  Qed.

  Lemma mem_add2 :
    forall x y s,
      S.E.eq x y ->
      S.mem x (S.add y s).
  Proof.
    move=> x y s H; apply/memP.
    move: (S.E.eq_sym H) => {H} H.
    exact: (S.add_1 _ H).
  Qed.

  Lemma mem_add3 :
    forall x y s,
      S.mem x s ->
      S.mem x (S.add y s).
  Proof.
    move=> x y s H; apply/memP.
    move/memP: H => H.
    exact: (S.add_2 _ H).
  Qed.

  Lemma mem_add_eq :
    forall x y s,
      S.E.eq x y ->
      S.mem x (S.add y s).
  Proof.
    move=> x y s Heq.
    apply: S.mem_1.
    apply: S.add_1.
    apply: S.E.eq_sym.
    assumption.
  Qed.

  Lemma mem_add_neq :
    forall x y s,
      ~ (S.E.eq x y) ->
      S.mem x (S.add y s) = S.mem x s.
  Proof.
    move=> x y s Hne.
    apply: add_neq_b.
    move=> Heq.
    apply: Hne.
    apply: S.E.eq_sym.
    assumption.
  Qed.

  Lemma not_mem_add1 :
    forall x y s,
      ~~ S.mem x (S.add y s) ->
      ~ S.E.eq x y /\ ~~ S.mem x s.
  Proof.
    move=> x y s /negP Hmem; split.
    - move=> Heq; apply: Hmem.
      exact: mem_add2.
    - apply/negP => H; apply: Hmem.
      exact: mem_add3.
  Qed.

  Lemma not_mem_add2 :
    forall x y s,
      ~ S.E.eq x y /\ ~~ S.mem x s ->
      ~~ S.mem x (S.add y s).
  Proof.
    move=> x y s [] Heq /negP Hmem.
    apply/negP => H; apply: Hmem.
    rewrite -(mem_add_neq _ Heq).
    assumption.
  Qed.

  Lemma mem_union1 :
    forall v s1 s2,
      S.mem v (S.union s1 s2) ->
      S.mem v s1 \/ S.mem v s2.
  Proof.
    move=> v s1 s2 /memP Hin.
    case: (S.union_1 Hin) => {Hin} /memP Hmem.
    - by left.
    - by right.
  Qed.

  Lemma mem_union2 :
    forall v s1 s2,
      S.mem v s1 ->
      S.mem v (S.union s1 s2).
  Proof.
    move=> v s1 s2 /memP Hin; apply/memP.
    exact: (S.union_2 _ Hin).
  Qed.

  Lemma mem_union3 :
    forall v s1 s2,
      S.mem v s2 ->
      S.mem v (S.union s1 s2).
  Proof.
    move=> v s1 s2 /memP Hin; apply/memP.
    exact: (S.union_3 _ Hin).
  Qed.

  Lemma not_mem_union1 :
    forall v s1 s2,
      ~~ S.mem v (S.union s1 s2) ->
      ~~ S.mem v s1 /\ ~~ S.mem v s2.
  Proof.
    move=> v s1 s2 /negP H; split; apply/negP => Hmem; apply: H.
    - exact: (mem_union2 _ Hmem).
    - exact: (mem_union3 _ Hmem).
  Qed.

  Lemma not_mem_union2 :
    forall v s1 s2,
      ~~ S.mem v s1 /\ ~~ S.mem v s2 ->
      ~~ S.mem v (S.union s1 s2).
  Proof.
    move=> v s1 s2 [] /negP H1 /negP H2; apply/negP => Hmem.
    case: (mem_union1 Hmem) => H3.
    - apply: H1; assumption.
    - apply: H2; assumption.
  Qed.

  Lemma mem_subset :
    forall v s1 s2,
      S.mem v s1 ->
      S.subset s1 s2 ->
      S.mem v s2.
  Proof.
    move=> v s1 s2 /memP Hin Hsub; apply/memP.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    exact: (Hsub _ Hin).
  Qed.

  Lemma union_emptyl s :
    S.Equal (S.union S.empty s) s.
  Proof.
    move=> v; split => Hin.
    - case: (S.union_1 Hin) => {Hin} Hin.
      + apply: False_ind.
        apply: S.empty_1.
        exact: Hin.
      + assumption.
    - apply: S.union_3.
      assumption.
  Qed.

  Lemma union_emptyr s :
    S.Equal (S.union s S.empty) s.
  Proof.
    rewrite OP.P.union_sym.
    exact: union_emptyl.
  Qed.

  Lemma union_subsets sa1 sa2 sb1 sb2 :
    S.subset sa1 sb1 ->
    S.subset sa2 sb2 ->
    S.subset (S.union sa1 sa2) (S.union sb1 sb2).
  Proof.
    move=> Hsub1 Hsub2.
    apply/S.subset_1 => x /memP Hmemx.
    apply/memP.
    move: (mem_union1 Hmemx) => {Hmemx} [] Hmemx.
    - apply: mem_union2.
      exact: (mem_subset Hmemx Hsub1).
    - apply: mem_union3.
      exact: (mem_subset Hmemx Hsub2).
  Qed.

  Lemma union_subset_equal s1 s2 :
    S.subset s1 s2 ->
    S.Equal (S.union s1 s2) s2.
  Proof.
    move=> /S.subset_2 Hsub.
    exact: (OP.P.union_subset_equal Hsub).
  Qed.

  Lemma union_subset_1 s1 s2 : S.subset s1 (S.union s1 s2).
  Proof.
    apply/S.subset_1.
    exact: OP.P.union_subset_1.
  Qed.

  Lemma union_subset_2 s1 s2 : S.subset s1 (S.union s2 s1).
  Proof.
    apply/S.subset_1.
    exact: OP.P.union_subset_2.
  Qed.

  Lemma subset_empty s :
    S.subset S.empty s.
  Proof.
    apply/S.subset_1.
    exact: OP.P.subset_empty.
  Qed.

  Lemma subset_union1 s1 s2 s3 :
    S.subset s1 s2 ->
    S.subset s1 (S.union s2 s3).
  Proof.
    move=> Hsub.
    apply: S.subset_1 => x /memP Hx.
    apply/memP.
    apply/mem_union2.
    exact: (mem_subset Hx Hsub).
  Qed.

  Lemma subset_union2 s1 s2 s3 :
    S.subset s1 s3 ->
    S.subset s1 (S.union s2 s3).
  Proof.
    rewrite OP.P.union_sym.
    exact: subset_union1.
  Qed.

  Lemma subset_union3 s1 s2 s3 :
    S.subset s1 s3 ->
    S.subset s2 s3 ->
    S.subset (S.union s1 s2) s3.
  Proof.
    move=> H13 H23.
    apply: S.subset_1.
    apply: OP.P.union_subset_3.
    - exact: (S.subset_2 H13).
    - exact: (S.subset_2 H23).
  Qed.

  Lemma subset_union4 s1 s2 s3 :
    S.subset (S.union s1 s2) s3 ->
    S.subset s1 s3.
  Proof.
    move=> Hsub.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    apply: S.subset_1 => x Hinx.
    apply: (Hsub x).
    exact: (S.union_2 _ Hinx).
  Qed.

  Lemma subset_union5 s1 s2 s3 :
    S.subset (S.union s1 s2) s3 ->
    S.subset s2 s3.
  Proof.
    rewrite OP.P.union_sym.
    exact: subset_union4.
  Qed.

  Lemma mem_in_elements :
    forall x s,
      S.mem x s ->
      InA S.E.eq x (S.elements s).
  Proof.
    move=> x s Hmem.
    apply: S.elements_1.
    apply/memP.
    assumption.
  Qed.

  Lemma in_elements_mem :
    forall x s,
      InA S.E.eq x (S.elements s) ->
      S.mem x s.
  Proof.
    move=> x s Hin.
    apply/memP.
    apply: S.elements_2.
    assumption.
  Qed.

  Lemma subset_refl :
    forall s, S.subset s s.
  Proof.
    move=> s; apply: S.subset_1.
    exact: OP.P.subset_refl.
  Qed.

  Lemma subset_trans :
    forall s1 s2 s3, S.subset s1 s2 -> S.subset s2 s3 -> S.subset s1 s3.
  Proof.
    move=> s1 s2 s3 H12 H23.
    move: (S.subset_2 H12) => {H12} H12.
    move: (S.subset_2 H23) => {H23} H23.
    apply: S.subset_1.
    exact: (OP.P.subset_trans H12 H23).
  Qed.

  Lemma subset_add :
    forall v s1 s2,
      S.subset s1 s2 ->
      S.subset s1 (S.add v s2).
  Proof.
    move=> v s1 s2 Hsub.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    apply: S.subset_1 => x Hin.
    move: (Hsub x Hin) => {Hin} Hin.
    exact: (S.add_2 _ Hin).
  Qed.

  Lemma subset_add3 x s1 s2 :
    S.mem x s2 -> S.subset s1 s2 -> S.subset (S.add x s1) s2.
  Proof.
    move=> /memP Hin Hsub.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    apply/S.subset_1.
    exact: OP.P.subset_add_3.
  Qed.

  Lemma subset_add2 x s1 s2 :
    S.subset s1 s2 -> S.subset s1 (S.add x s2).
  Proof.
    move=> Hsub.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    apply/S.subset_1.
    exact: OP.P.subset_add_2.
  Qed.

  Lemma mem_empty :
    forall v,
      S.mem v S.empty = false.
  Proof.
    move=> v.
    apply/memP => Hin.
    move: (S.empty_1) => Hemp.
    move: (Hemp v); apply.
    assumption.
  Qed.

  Lemma Empty_mem :
    forall v s,
      S.Empty s ->
      S.mem v s = false.
  Proof.
    move=> v s Hemp.
    apply/memP => Hin.
    exact: (Hemp v Hin).
  Qed.

  Lemma in_of_list1 x s :
    S.In x (OP.P.of_list s) -> InA S.E.eq x s.
  Proof.
    move=> Hin.
    move: (OP.P.of_list_1 s x) => [H1 H2].
    exact: (H1 Hin).
  Qed.

  Lemma in_of_list2 x s :
    InA S.E.eq x s -> S.In x (OP.P.of_list s).
  Proof.
    move=> Hin.
    move: (OP.P.of_list_1 s x) => [H1 H2].
    exact: (H2 Hin).
  Qed.

  Lemma mem_of_list1 x s :
    S.mem x (OP.P.of_list s) -> InA S.E.eq x s.
  Proof.
    move=> /memP Hin.
    exact: in_of_list1.
  Qed.

  Lemma mem_of_list2 x s :
    InA S.E.eq x s -> S.mem x (OP.P.of_list s).
  Proof.
    move=> Hin; apply/memP.
    exact: in_of_list2.
  Qed.

  Lemma mem_remove1 x y s :
    S.mem x (S.remove y s) ->
    ~ S.E.eq x y /\ S.mem x s.
  Proof.
    move=> Hmem; split.
    - move=> Heq.
      move: (S.E.eq_sym Heq) => {Heq} Heq.
      apply: (@S.remove_1 s y x Heq).
      apply/memP.
      assumption.
    - apply/memP; apply: (@S.remove_3 s y x); apply/memP; assumption.
  Qed.

  Lemma mem_remove2 x y s :
    S.E.eq x y ->
    ~~ S.mem x (S.remove y s).
  Proof.
    move=> Heq.
    apply/negP => Hmem.
    move: (mem_remove1 Hmem) => {Hmem} [Hne Hmem].
    apply: Hne; assumption.
  Qed.

  Lemma mem_remove3 x y s :
    ~ S.E.eq x y ->
    S.mem x s ->
    S.mem x (S.remove y s).
  Proof.
    move=> Hne Hmem.
    apply/memP; apply: S.remove_2.
    - move=> Heq; apply: Hne; apply: S.E.eq_sym; assumption.
    - apply/memP; assumption.
  Qed.

  Lemma in_remove_ne x y s :
    S.In x (S.remove y s) -> ~ S.E.eq x y.
  Proof.
    move=> Hin Heq.
    move: (S.E.eq_sym Heq) => {Heq} Heq.
    exact: (S.remove_1 Heq Hin).
  Qed.

  Lemma diff_add x s1 s2 :
    S.Equal (S.diff s1 (S.add x s2)) (S.remove x (S.diff s1 s2)).
  Proof.
    split => Hin.
    - apply: S.remove_2.
      + move=> Heq; apply: (S.diff_2 Hin).
        exact: (S.add_1 _ Heq).
      + apply: (S.diff_3 (S.diff_1 Hin)).
        move=> H; apply: (S.diff_2 Hin).
        exact: (S.add_2 _ H).
    - apply: S.diff_3.
      + exact: (S.diff_1 (S.remove_3 Hin)).
      + move: (OP.P.Add_add s2 x a).
        move=> [H _].
        move=> H1; case: (H H1) => {H H1}.
        * move=> Heq.
          move: (S.E.eq_sym Heq) => {Heq} Heq.
          exact: (in_remove_ne Hin Heq).
        * move=> Hins2.
          exact: (S.diff_2 (S.remove_3 Hin) Hins2).
  Qed.

  Lemma subset_union_diff1 s1 s2 s3 :
    S.subset s1 (S.union s2 s3) ->
    S.subset (S.diff s1 s2) s3.
  Proof.
    move=> H.
    apply: S.subset_1 => x Hin_diff.
    move: (S.subset_2 H) => {H} H.
    move: (H x (S.diff_1 Hin_diff)) => Hin_union.
    case: (S.union_1 Hin_union).
    - move=> Hin2.
      apply: False_ind; exact: (S.diff_2 Hin_diff Hin2).
    - by apply.
  Qed.

  Lemma subset_union_diff2 s1 s2 s3 :
    S.subset s1 (S.union s2 s3) ->
    S.subset (S.diff s1 s3) s2.
  Proof.
    rewrite OP.P.union_sym.
    move=> H.
    exact: (subset_union_diff1 H).
  Qed.

  Lemma subset_union_diff3 s1 s2 :
    S.subset s1 (S.union (S.diff s1 s2) s2).
  Proof.
    apply: S.subset_1 => x Hinx.
    case Hmem: (S.mem x s2).
    - apply: S.union_3.
      apply/memP; assumption.
    - apply: S.union_2.
      apply: (S.diff_3 Hinx).
      apply/memP.
      by rewrite Hmem.
  Qed.

  Lemma subset_union_diff4 s1 s2 s3 :
    S.subset (S.diff s1 s2) s3 ->
    S.subset s1 (S.union s2 s3).
  Proof.
    move=> H.
    move: (S.subset_2 H) => {H} H.
    apply/S.subset_1 => x Hinx.
    case H2: (S.mem x s2).
    - apply: S.union_2.
      apply/memP; assumption.
    - apply: S.union_3.
      apply: (H x).
      apply: (S.diff_3 Hinx).
      apply/memP.
      by rewrite H2.
  Qed.

  Lemma mem_inter1 x s1 s2 :
    S.mem x (S.inter s1 s2) -> S.mem x s1.
  Proof.
    move=> /memP H.
    apply/memP.
    exact: (S.inter_1 H).
  Qed.

  Lemma mem_inter2 x s1 s2 :
    S.mem x (S.inter s1 s2) -> S.mem x s2.
  Proof.
    move=> /memP H.
    apply/memP.
    exact: (S.inter_2 H).
  Qed.

  Lemma mem_inter3 x s1 s2 :
    S.mem x s1 -> S.mem x s2 ->
    S.mem x (S.inter s1 s2).
  Proof.
    move=> /memP H1 /memP H2.
    apply/memP.
    exact: (S.inter_3 H1 H2).
  Qed.



  Definition disjoint s1 s2 : bool :=
    S.is_empty (S.inter s1 s2).

  Lemma disjoint_sym s1 s2 :
    disjoint s1 s2 = disjoint s2 s1.
  Proof.
    rewrite /disjoint OP.P.inter_sym.
    reflexivity.
  Qed.

  Lemma disjoint_nonempty_anti_refl s : ~~ S.is_empty s -> ~~ disjoint s s.
  Proof.
    move=> Hemp.
    apply/negP => H.
    move/negP: Hemp; apply.
    move: H.
    by rewrite /disjoint OP.P.inter_subset_equal.
  Qed.

  Lemma mem_disjoint1 x s1 s2 :
    disjoint s1 s2 ->
    S.mem x s1 -> ~~ S.mem x s2.
  Proof.
    move=> Hd Hm1.
    apply/negP => Hm2.
    move: (S.is_empty_2 Hd) => {Hd} Hd.
    apply: (Hd x).
    apply/memP.
    exact: (mem_inter3 Hm1 Hm2).
  Qed.

  Lemma mem_disjoint2 x s1 s2 :
    disjoint s1 s2 ->
    S.mem x s2 -> ~~ S.mem x s1.
  Proof.
    rewrite disjoint_sym.
    exact: mem_disjoint1.
  Qed.

  Lemma disjoint_singleton x s :
    disjoint s (S.singleton x) = ~~ S.mem x s.
  Proof.
    case H: (S.mem x s) => /=.
    - apply/negP => Hd.
      move: (S.is_empty_2 Hd) => Hemp.
      apply: (Hemp x).
      apply/memP.
      apply: (mem_inter3 H).
      exact: mem_singleton2.
    - move/negP: H => H.
      apply: S.is_empty_1 => v /memP Hv.
      apply: H.
      rewrite -(mem_singleton1 (mem_inter2 Hv)).
      exact: (mem_inter1 Hv).
  Qed.

  Lemma disjoint_add x s1 s2 :
    disjoint s1 (S.add x s2) = ~~ S.mem x s1 && disjoint s1 s2.
  Proof.
    case Hx: (S.mem x s1) => /=.
    - apply/negP => Hd.
      move: (S.is_empty_2 Hd) => Hemp.
      apply: (Hemp x).
      apply/memP.
      apply: (mem_inter3 Hx).
      exact: mem_add2.
    - case Hd12: (disjoint s1 s2) => /=.
      + apply: S.is_empty_1 => v /memP Hv.
        move: (mem_inter1 Hv) (mem_inter2 Hv) => {Hv} Hv1 Hv2.
        move: (S.is_empty_2 Hd12) => {Hd12} Hemp.
        apply: (Hemp v) => {Hemp}.
        apply/memP.
        apply: (mem_inter3 Hv1).
        case: (mem_add1 Hv2); last by apply.
        move=> H.
        apply: False_ind.
        move/negP: Hx; apply.
        rewrite -H; assumption.
      + apply/negP => Hd.
        move/negP: Hd12; apply.
        apply: S.is_empty_1 => v /memP Hv.
        move: (S.is_empty_2 Hd) => {Hd} Hemp.
        apply: (Hemp v).
        apply/memP.
        apply: (mem_inter3 (mem_inter1 Hv)).
        apply: mem_add3.
        exact: (mem_inter2 Hv).
  Qed.

  Lemma subset_union_disjoint1 s1 s2 s3 :
    S.subset s1 (S.union s2 s3) ->
    disjoint s1 s3 ->
    S.subset s1 s2.
  Proof.
    move=> Hsub Hd.
    apply: S.subset_1 => x /memP Hmem1.
    apply/memP.
    case: (mem_union1 (@mem_subset x _ _ Hmem1 Hsub)).
    - done.
    - move=> Hmem3.
      apply: False_ind.
      apply/negP/negPn: (mem_disjoint1 Hd Hmem1).
      assumption.
  Qed.

  Lemma subset_union_disjoint2 s1 s2 s3 :
    S.subset s1 (S.union s2 s3) ->
    disjoint s1 s2 ->
    S.subset s1 s3.
  Proof.
    rewrite OP.P.union_sym.
    exact: subset_union_disjoint1.
  Qed.

End FSetLemmas.

Module Make (V : SsrOrderedType).
  Module S := FSetList.Make V.
  Module Lemmas := FSetLemmas(S).
  Include S.
End Make.



Module Map2 (S1 S2 : FSetInterface.S).

  Module Lemmas1 := FSetLemmas(S1).
  Module Lemmas2 := FSetLemmas(S2).

  Notation of_list := Lemmas2.OP.P.of_list.

  Definition preserve f : Prop :=
    forall x y, S1.E.eq x y -> S2.E.eq (f x) (f y).

  Definition injective f : Prop :=
    forall x y, S2.E.eq (f x) (f y) -> S1.E.eq x y.

  Record well_map2 f : Prop :=
    mkWellMap2 { f_preserve : preserve f;
                 f_injective : injective f }.

  Section Map2.

    Variable f : S1.elt -> S2.elt.

    Variable well : well_map2 f.

    Definition map2 s :=
      of_list (map f (S1.elements s)).

    Lemma inA_map1 x s :
      InA S1.E.eq x s ->
      InA S2.E.eq (f x) (map f s).
    Proof.
      elim: s x => /=.
      - move=> x H; by inversion H.
      - move=> hd tl IH x Hin.
        inversion_clear Hin.
        + apply: InA_cons_hd.
          exact: (f_preserve well).
        + apply: InA_cons_tl.
          exact: (IH _ H).
    Qed.

    Lemma inA_map2 x s :
      InA S2.E.eq (f x) (map f s) ->
      InA S1.E.eq x s.
    Proof.
      elim: s x => /=.
      - move=> x H; by inversion H.
      - move=> hd tl IH x Hin.
        inversion_clear Hin.
        + apply: InA_cons_hd.
          exact: (f_injective well H).
        + apply: InA_cons_tl.
          exact: (IH _ H).
    Qed.

    Lemma inA_map3 x s :
      InA S2.E.eq x (map f s) ->
      exists y, S2.E.eq x (f y) /\ InA S1.E.eq y s.
    Proof.
      elim: s x => /=.
      - move=> x H; by inversion H.
      - move=> hd tl IH x Hin.
        inversion_clear Hin.
        + exists hd; split.
          * assumption.
          * exact: InA_cons_hd.
        + move: (IH _ H) => [y [Heq HinA]].
          exists y; split.
          * assumption.
          * exact: InA_cons_tl.
    Qed.

    Lemma map2_Empty1 s :
      S1.Empty s ->
      S2.Empty (map2 s).
    Proof.
      move=> Hemp1.
      rewrite /map2.
      move=> x Hin.
      move: (Lemmas1.OP.P.elements_Empty s) => [H _].
      rewrite (H Hemp1) /= in Hin => {H}.
      move: (Lemmas2.empty_iff x) => [H _].
      apply: H; assumption.
    Qed.

    Lemma map2_Empty2 s :
      S2.Empty (map2 s) ->
      S1.Empty s.
    Proof.
      move=> Hemp1.
      rewrite /map2 in Hemp1.
      move=> x Hmem.
      apply: (Hemp1 (f x)).
      apply: Lemmas2.in_of_list2.
      apply: inA_map1.
      exact: (S1.elements_1 Hmem).
    Qed.

    Lemma map2_mem1 x xs :
      S2.mem (f x) (map2 xs) = S1.mem x xs.
    Proof.
      rewrite /map2.
      case Hmem1: (S1.mem x xs).
      - apply: Lemmas2.mem_of_list2.
        apply: inA_map1.
        move/Lemmas1.memP: Hmem1 => Hin1.
        exact: (S1.elements_1 Hin1).
      - apply/negP => Hmem2.
        move/negP: Hmem1; apply.
        move: (Lemmas2.mem_of_list1 Hmem2) => HinA.
        move: (inA_map2 HinA) => {HinA} HinA.
        apply/Lemmas1.memP.
        exact: (S1.elements_2 HinA).
    Qed.

    Lemma map2_mem2 x xs :
      S2.mem x (map2 xs) ->
      exists y, S2.E.eq x (f y) /\ S1.mem y xs.
    Proof.
      rewrite /map2 => Hmem.
      move: (Lemmas2.mem_of_list1 Hmem) => {Hmem} HinA.
      move: (inA_map3 HinA) => {HinA} [y [Heq HinA]].
      exists y; split.
      - assumption.
      - apply/Lemmas1.memP.
        exact: S1.elements_2.
    Qed.

    Lemma map2_singleton x :
      S2.Equal (map2 (S1.singleton x)) (S2.singleton (f x)).
    Proof.
      move=> v; split => /Lemmas2.memP Hmem; apply: Lemmas2.memP.
      - move: (map2_mem2 Hmem) => [y [Hy Hmemy]].
        apply: Lemmas2.mem_singleton2.
        rewrite Hy.
        exact: (f_preserve _ (Lemmas1.mem_singleton1 Hmemy)).
      - rewrite (Lemmas2.mem_singleton1 Hmem) map2_mem1.
        apply: Lemmas1.mem_singleton2.
        exact: S1.E.eq_refl.
    Qed.

    Lemma map2_add v s :
      S2.Equal (map2 (S1.add v s)) (S2.add (f v) (map2 s)).
    Proof.
      move=> x; split; move=> /Lemmas2.memP Hmem; apply/Lemmas2.memP.
      - move: (map2_mem2 Hmem) => [y [Hfy Hmemy]].
        case: (Lemmas1.mem_add1 Hmemy) => {Hmemy} Hy.
        + rewrite Hfy.
          apply: Lemmas2.mem_add2.
          exact: (f_preserve _ Hy).
        + apply: Lemmas2.mem_add3.
          rewrite Hfy map2_mem1.
          assumption.
      - case: (Lemmas2.mem_add1 Hmem) => {Hmem} Hx.
        + rewrite Hx map2_mem1.
          exact: Lemmas1.mem_add2.
        + move: (map2_mem2 Hx) => [y [Hfy Hmemy]].
          rewrite Hfy map2_mem1.
          apply: Lemmas1.mem_add3.
          assumption.
    Qed.

    Lemma map2_union s1 s2 :
      S2.Equal (map2 (S1.union s1 s2))
               (S2.union (map2 s1) (map2 s2)).
    Proof.
      move=> x; split; move=> /Lemmas2.memP Hmem; apply/Lemmas2.memP.
      - move: (map2_mem2 Hmem) => [y [Hy Hmemy]].
        case: (Lemmas1.mem_union1 Hmemy) => {Hmemy} Hmemy.
        + apply: Lemmas2.mem_union2.
          rewrite Hy map2_mem1.
          assumption.
        + apply: Lemmas2.mem_union3.
          rewrite Hy map2_mem1.
          assumption.
      - case: (Lemmas2.mem_union1 Hmem) => {Hmem} Hmemx.
        + move: (map2_mem2 Hmemx) => [y [Hy Hmemy]].
          rewrite Hy map2_mem1.
          apply/Lemmas1.mem_union2; assumption.
        + move: (map2_mem2 Hmemx) => [y [Hy Hmemy]].
          rewrite Hy map2_mem1.
          apply/Lemmas1.mem_union3; assumption.
    Qed.

    Lemma mem_map2_union x s1 s2 :
      S2.mem x (map2 (S1.union s1 s2)) =
      (S2.mem x (map2 s1)) || (S2.mem x (map2 s2)).
    Proof.
      rewrite map2_union.
      rewrite Lemmas2.F.union_b.
      reflexivity.
    Qed.

    Lemma map2_union1 x s1 s2 :
      S2.mem x (map2 (S1.union s1 s2)) ->
      S2.mem x (map2 s1) \/ S2.mem x (map2 s2).
    Proof.
      rewrite map2_union => Hmem.
      case: (Lemmas2.mem_union1 Hmem); [by left | by right].
    Qed.

    Lemma map2_union2 x s1 s2 :
      S2.mem x (map2 s1) ->
      S2.mem x (map2 (S1.union s1 s2)).
    Proof.
      rewrite map2_union => Hmem.
      apply: Lemmas2.mem_union2; assumption.
    Qed.

    Lemma map2_union3 x s1 s2 :
      S2.mem x (map2 s2) ->
      S2.mem x (map2 (S1.union s1 s2)).
    Proof.
      rewrite map2_union => Hmem.
      apply: Lemmas2.mem_union3; assumption.
    Qed.

  End Map2.

End Map2.