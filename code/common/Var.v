
(** * Variables *)

From Coq Require Import FMaps FSets ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Common Require Import FMaps FSets ZAriths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope N_scope.

Definition var : Set := N.

Module VarOrder := NOrder.

(* Variable sets. *)

Module VS.
  Module S := FSetList.Make(NOrder).
  Module Lemmas := FSetLemmas(S).
  Include S.

  (* Generate a new variable. *)
  Definition new_var (s : t) : var :=
    match max_elt s with
    | Some v => v + 1
    | None => 0
    end.

  Lemma new_var_is_new :
    forall (s : t), ~~ mem (new_var s) s.
  Proof.
    move=> s.
    apply/negP => Hmem.
    move: (mem_2 Hmem) => {Hmem}.
    rewrite /new_var.
    case H: (max_elt s).
    - move=> Hin.
      move: (max_elt_2 H Hin) => Hfalse.
      apply: Hfalse.
      exact: NltnSn.
    - move: (max_elt_3 H) => {H} H Hin.
      move: (H 0) => Hnotin; apply: Hnotin; exact: Hin.
  Qed.

End VS.



(* Variable maps. *)

Module VM.
   Module M := FMapList.Make(NOrder).
   Module Lemmas := FMapLemmas(M).
   Include M.

   Section Aux.

     Variable elt : Type.

     (* Convert a variable map to a variable set. *)
     Definition vset (m : M.t elt) : VS.t :=
       fold (fun x _ s => VS.add x s) m VS.empty.

     Lemma mem_vset E :
       forall x, mem x E -> VS.mem x (vset E).
     Proof.
       rewrite /vset.
       eapply Lemmas.P.fold_rec.
       - move=> m Hempty x Hmem.
         apply: False_ind.
         exact: (Lemmas.empty_mem Hempty Hmem).
       - move=> x e m E1 E2 _ _ Hadd Hind y Hmem.
         case Hyx: (y == x).
         + exact: (VS.Lemmas.mem_add_eq _ Hyx).
         + move/negP: Hyx => Hyx.
           rewrite (VS.Lemmas.mem_add_neq _ Hyx).
           apply: Hind.
           move: (Hadd y) => {Hadd}.
           rewrite (VM.Lemmas.find_add_neq _ _ Hyx) => {Hyx} Hfind.
           rewrite -(VM.Lemmas.find_eq_mem_eq Hfind).
           exact: Hmem.
     Qed.

     (* Generate a new variable. *)
     Definition new_var (m : t elt) : var :=
       match Lemmas.max_elt m with
       | Some (v, _) => v + 1
       | None => 0
       end.

     Lemma new_var_is_new :
       forall (m : t elt), ~~ mem (new_var m) m.
     Proof.
       move=> m.
       apply/negP => Hmem.
       move: (mem_2 Hmem) => {Hmem}.
       rewrite /new_var.
       move: (refl_equal (Lemmas.max_elt m)).
       move: {2}(Lemmas.max_elt m) => x.
       destruct x.
       - destruct p as [x ty].
         move=> Hmax; rewrite Hmax => Hin.
         move: (Lemmas.max_elt_Above Hmax) => Habove.
         have: In (x + 1) (remove x m).
         + case: Hin => ty1 Hmapsto.
           exists ty1.
           apply: (remove_2 _ Hmapsto).
           move=> {Hmax Habove Hmapsto ty ty1 m} Heq.
           move: (NltnSn x).
           rewrite {1}(eqP Heq).
           rewrite Nltnn.
           discriminate.
         + move=> Hin1.
           move: (Habove _ Hin1) => Hlt.
           move: (Nltn_trans Hlt (NltnSn x)).
           rewrite Nltnn.
           discriminate.
       - move=> Hmax; rewrite Hmax => Hin.
         move: (Lemmas.max_elt_Empty Hmax) => Hempty.
         case: Hin => ty Hmapsto.
         move: (Hempty 0 ty).
         apply; assumption.
     Qed.

   End Aux.

End VM.

Close Scope N_scope.