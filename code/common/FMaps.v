
(** * Some auxiliary lemmas for FMaps. *)

(** These lemmas can be proven by facts in Coq.FSets.FMapFacts. *)

From Coq Require Import FMaps OrderedType.
From mathcomp Require Import ssreflect ssrbool.
From Common Require Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Module FMapLemmas (M : FMapInterface.S).

  Module F := Facts(M).
  Module OP := OrdProperties(M).
  Include F.
  Include OP.

  Section FMapLemmas.

    Local Notation key := M.E.t.

    Variable elt elt' : Type.

    Lemma memP k (m : M.t elt) : reflect (M.In k m) (M.mem k m).
    Proof.
      case H: (M.mem k m).
      - apply: ReflectT.
        exact: (M.mem_2 H).
      - apply: ReflectF.
        move=> Hin; move: (M.mem_1 Hin).
        rewrite H; discriminate.
    Qed.

    Lemma find_add_eq (m : M.t elt) (x y : key) (e : elt) :
      M.E.eq x y -> M.find x (M.add y e m) = Some e.
    Proof.
      move=> Hxy.
      apply: F.add_eq_o.
      apply: M.E.eq_sym.
      exact: Hxy.
    Qed.

    Lemma find_add_neq (m : M.t elt) (x y : key) (e : elt) :
      ~(M.E.eq x y) -> M.find x (M.add y e m) = M.find x m.
    Proof.
      move=> Hne.
      apply: F.add_neq_o.
      move=> Heq; apply: Hne; apply: M.E.eq_sym.
      exact: Heq.
    Qed.

    Lemma find_some_map (f : elt -> elt') (m : M.t elt) (x : key) (e : elt) :
      M.find x m = Some e ->
      M.find x (M.map f m) = Some (f e).
    Proof.
      move=> H.
      rewrite F.map_o.
      rewrite /option_map.
      rewrite H.
      reflexivity.
    Qed.

    Lemma find_none_map (f : elt -> elt') (m : M.t elt) (x : key) :
      M.find x m = None ->
      M.find x (M.map f m) = None.
    Proof.
      move=> H.
      rewrite F.map_o.
      rewrite /option_map.
      rewrite H.
      reflexivity.
    Qed.

    Lemma find_map_some (f : elt -> elt') (m : M.t elt) (x : key) (e : elt') :
      M.find x (M.map f m) = Some e ->
      exists a, e = f a /\ M.find x m = Some a.
    Proof.
      move=> H.
      move: (M.find_2 H) => {H} H.
      case: (F.map_mapsto_iff m x e f) => Hf _.
      move: (Hf H) => {H Hf} [] => a [Hea Hxa].
      exists a.
      split.
      - assumption.
      - apply: M.find_1.
        assumption.
    Qed.

    Lemma find_map_none (f : elt -> elt') (m : M.t elt) (x : key) :
      M.find x (M.map f m) = None ->
      M.find x m = None.
    Proof.
      rewrite F.map_o.
      rewrite /option_map.
      case: (M.find x m).
      - discriminate.
      - reflexivity.
    Qed.

    Lemma empty_mem (m : M.t elt) (x : key) :
      M.Empty m -> M.mem x m -> False.
    Proof.
      move=> Hempty Hmem.
      move/memP: Hmem => [e Hmapsto].
      move: (Hempty x e); apply.
      exact: Hmapsto.
    Qed.

    Lemma find_eq_mem_eq (m1 m2 : M.t elt) (x1 x2 : key) :
      M.find x1 m1 = M.find x2 m2 -> M.mem x1 m1 = M.mem x2 m2.
    Proof.
      case Hfind1: (M.find x1 m1);
      move=> Hfind2;
      rewrite mem_find_b mem_find_b Hfind1 -Hfind2;
      reflexivity.
    Qed.

    Lemma find_some_mem (m : M.t elt) (x : key) (v : elt) :
      M.find x m = Some v ->
      M.mem x m.
    Proof.
      move=> Hfind.
      move: (M.find_2 Hfind) => Hmapsto.
      apply: M.mem_1.
      exists v; assumption.
    Qed.

    Lemma find_none_mem (m : M.t elt) (x : key) :
      M.find x m = None ->
      ~~ (M.mem x m).
    Proof.
      move=> Hfind.
      apply/negP=> Hmem.
      move: (M.mem_2 Hmem) => [v Hmapsto].
      move: (M.find_1 Hmapsto).
      rewrite Hfind; discriminate.
    Qed.

    Lemma Empty_In (m : M.t elt) (x : key) :
      M.Empty m -> ~ (M.In x m).
    Proof.
      move=> Hemp Hin.
      case: Hin => [v Hmapsto].
      exact: (Hemp x v Hmapsto).
    Qed.

    Lemma Empty_mem (m : M.t elt) (x : key) :
      M.Empty m -> ~~ (M.mem x m).
    Proof.
      move=> Hemp.
      apply/negP => Hmem.
      move/memP: Hmem.
      exact: Empty_In.
    Qed.

    Lemma Empty_find (m : M.t elt) (x : key) :
      M.Empty m -> M.find x m = None.
    Proof.
      move=> Hemp.
      move: (not_find_in_iff m x) => [H _].
      apply: H => H.
      exact: (Empty_In Hemp H).
    Qed.

  End FMapLemmas.

End FMapLemmas.

Module Make (V : SsrOrderedType).
  Module M := FMapList.Make V.
  Module Lemmas := FMapLemmas(M).
  Include M.
End Make.