
(** * Typing Environments *)

From Coq Require Import Program Program.Tactics ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Common Require Import HList Var ZAriths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Environments for variables with the same type. *)

Module SEnv.

  Definition t : Type := VS.t.

  Definition empty : t := VS.empty.

  (* Check if a variable is defined in an environment. *)
  Definition mem (v : var) (E : t) : bool := VS.mem v E.

  Definition add (v : var) (E : t) : t := VS.add v E.

  Inductive pvar (E : t) : Set :=
  | PVar : forall x : var, VS.mem x E -> pvar E.

  Definition pvar_var (E : t) (x : pvar E) : var :=
    match x with
    | PVar v _ => v
    end.

  (* Create a new variable. *)

  Definition new_var (E : t) : var := VS.new_var E.

  Lemma new_var_is_new :
    forall (E : t), ~~ mem (new_var E) E.
  Proof.
    exact: VS.new_var_is_new.
  Qed.

End SEnv.



(** Environments for variables with heterogeneous types. *)

Module TEnv.

  Section Env.

    (* Variable types. *)
    Variable T : Set.

    Definition t : Type := VM.t T.

    Definition empty : t := VM.empty T.

    (* Check if a variable is defined in an environment. *)
    Definition mem (v : var) (E : t) : bool := VM.mem v E.

    (* Find the type of a variable in an environment. *)
    Definition find (v : var) (E : t) : option T := VM.find v E.

    Definition add (v : var) (ty : T) (E : t) : t := VM.add v ty E.

    Inductive pvar (E : t) : Set :=
    | PVar : forall (x : var) (ty : T), find x E = Some ty -> pvar E.

    Definition pvar_var (E : t) (x : pvar E) : var :=
      match x with
      | PVar v _ _ => v
      end.

    Definition pvar_ty (E : t) (x : pvar E) : T :=
      match x with
      | PVar _ ty _ => ty
      end.

    (* Create a new variable. *)

    Definition new_var (E : t) : var := VM.new_var E.

    Lemma new_var_is_new :
      forall (E : t), ~~ mem (new_var E) E.
    Proof.
      exact: VM.new_var_is_new.
    Qed.

    (* Convert to SEnv. *)

    Definition to_senv (E : t) : SEnv.t := VM.vset E.

    Lemma mem_to_senv E :
      forall x, mem x E -> SEnv.mem x (to_senv E).
    Proof.
      exact: VM.mem_vset.
    Qed.

  End Env.

End TEnv.



(** Environments for variables with heterogeneous types. Indices for the access
 of values in a heterogeneous list (HList) are defined in the environments. *)

Module HEnv.

  Section Env.

  Local Open Scope hlist_scope.

  (* Variable type. *)
  Variable T : Set.

  Record entry (types : list T) := mkEntry { vty : T;
                                             vin: bool;
                                             vidx : lidx vty types }.

  Record t := mkEnv { vtypes : list T;
                      vmap : VM.t (entry vtypes);
                      lidx_disjoint :
                        forall (x y : var) (ex ey : entry vtypes),
                          VM.find x vmap = Some ex ->
                          VM.find y vmap = Some ey ->
                          x != y ->
                          vidx ex <>i vidx ey }.

  Program Definition empty : t := {| vtypes := nil;
                                     vmap := VM.empty (entry nil) |}.

  (* Check if a variable is defined in an environment. *)
  Definition mem (v : var) (E : t) : bool := VM.mem v (vmap E).

  (* Find the entry of a variable in an environment. *)
  Definition find (v : var) (E : t) : option (entry (vtypes E)) :=
    VM.find v (vmap E).

  (* Find the type of a variable in an environment. *)
  Definition find_type (v : var) (E : t) : option T :=
    match find v E with
    | None => None
    | Some e => Some (vty e)
    end.

  (* Prepend a vtype to an entry. *)
  Definition prepend_vtype_to_entry {ty : T} {types : list T} (e : entry types) : entry (ty::types) :=
    {| vty := vty e;
       vin := vin e;
       vidx := HIS ty (vidx e) |}.

  (* Prepend a vtype to the list of variable types of an environment. *)
  Definition prepend_vtype (ty : T) (types : list T)
             (m : VM.t (entry types)) : VM.t (entry (ty::types)) :=
    VM.map (prepend_vtype_to_entry (ty:=ty) (types:=types)) m.

  (* Declare a program variable in an environment. *)
  Program Definition add_var (v : var) (ty : T) (input : bool) (E : t) : t :=
    {| vtypes := ty::(vtypes E);
       vmap := VM.add v {| vty := ty; vin := input; vidx := HI0 ty (vtypes E) |}
                      (prepend_vtype ty (vmap E)) |}.
  Next Obligation.
    case Hxv: (x == v); move/idP: Hxv => Hxv.
    - (* x == v *)
      case Hyv: (y == v); move/idP: Hyv => Hyv.
      + (* y == v *)
        rewrite (eqP Hxv) (eqP Hyv) in H1.
        apply: False_ind; apply: (negP H1); reflexivity.
      + (* y != v *)
        rewrite (VM.Lemmas.find_add_eq _ _ (Hxv)) in H;
        rewrite (VM.Lemmas.find_add_neq _ _ Hyv) /prepend_vtype in H0 =>
        {H1 Hxv Hyv}.
        case: H => H; rewrite -H /= => {H}.
        move: (VM.Lemmas.find_map_some H0) => {H0} [ey' [He_ey _]].
        rewrite He_ey /prepend_vtype_to_entry /=.
        move=> Heq; by inversion Heq.
    - (* x != v *)
      rewrite (VM.Lemmas.find_add_neq _ _ Hxv) /prepend_vtype in H => {Hxv}.
      move: (VM.Lemmas.find_map_some H) => {H} [ex' [He_ex He_x]].
      rewrite He_ex /prepend_vtype_to_entry /= => {He_ex}.
      case Hyv: (y == v); move/idP: Hyv => Hyv.
      + (* y == v *)
        rewrite (VM.Lemmas.find_add_eq _ _ Hyv) in H0 => {Hyv}.
        case: H0 => H0; rewrite -H0 /= => {H0}.
        move=> Heq; by inversion Heq.
      + (* y != v *)
        rewrite (VM.Lemmas.find_add_neq _ _ Hyv) /prepend_vtype in H0 => {Hyv}.
        move: (VM.Lemmas.find_map_some H0) => {H0} [ey' [He_ey He_y]].
        rewrite He_ey /prepend_vtype_to_entry /= => {He_ey}.
        move: (lidx_disjoint He_x He_y H1) => Hne Heq; apply: Hne.
        exact: (his_eq_lidx_eq Heq).
  Qed.

  (* Declare an input variable in an environment. *)
  Definition add_input (v : var) (ty : T) (E : t) : t :=
    add_var v ty true E.

  (* Declare a local variable in an environment. *)
  Definition add_local (v : var) (ty : T) (E : t) : t :=
    add_var v ty false E.

  (* A pvar is a variable of a specified type defined in an environment. *)
  (* Note: The equality of vtypes used here is =, not ==. If == is used, then
   * we will fail to do dependent destruction.
   *)
  Inductive pvar (E : t) (ty : T) : Set :=
  | PVar : forall v e, find v E = Some e -> vty e = ty -> pvar E ty.

  (* A any_pvar is a defined variable in an environment. *)
  Inductive any_pvar (E : t) : Set :=
  | AnyPVar : forall (v : var) (ty : T), pvar E ty -> any_pvar E.

  (* Return the variable ID of a pvar. *)
  Definition pvar_var (E : t) ty (x : pvar E ty) : var :=
    match x with
    | PVar v _ _ _ => v
    end.

  (* Return the entry of a pvar in an environment. *)
  Definition pvar_entry (E : t) ty (x : pvar E ty) : entry (vtypes E) :=
    match x with
    | PVar _ e _ _ => e
    end.

  (* Return the lidx of a pvar in an environment. *)
  Program Definition pvar_lidx (E : t) ty (x : pvar E ty) : lidx ty (vtypes E) :=
    match x with
    | PVar _ e _ _ => Env.vidx e
    end.

  (* Lemmas about pvar. *)

  Lemma pvar_vtype_eq (E : t) (ty1 ty2 : T) (x : pvar E ty1) (y : pvar E ty2) :
    pvar_var x == pvar_var y -> ty1 = ty2.
  Proof.
    elim: x => x ex Hex Htx /=.
    elim: y => y ey Hey Hty /=.
    move/eqP=> Hxy.
    rewrite -Hxy Hex in Hey.
    case: Hey => Hexey; rewrite -Hexey Htx in Hty.
    exact: Hty.
  Qed.

  Lemma pvar_lidx_heq (E : t) (tyx tyy : T) (x : pvar E tyx) (y : pvar E tyy) :
    pvar_var x == pvar_var y -> (pvar_lidx x =i pvar_lidx y)%hlist.
  Proof.
    elim: x => x ex Hex Htx /=.
    elim: y => y ey Hey Hty /=.
    move/eqP=> Hxy.
    dependent destruction Htx.
    dependent destruction Hty.
    rewrite /=.
    rewrite -Hxy Hex in Hey.
    case: Hey => Hey; rewrite Hey.
    reflexivity.
  Qed.

  Lemma pvar_lidx_eq (E : t) ty (x y : pvar E ty) :
    pvar_var x == pvar_var y -> pvar_lidx x = pvar_lidx y.
  Proof.
    move=> Hxy.
    apply: lidx_eq_eq.
    apply: pvar_lidx_heq.
    assumption.
  Qed.

  Lemma pvar_lidx_hneq (E : t) (tyx tyy : T) (x : pvar E tyx) (y : pvar E tyy) :
    pvar_var x != pvar_var y -> pvar_lidx x <>i pvar_lidx y.
  Proof.
    elim: x => x ex Hex Htx.
    elim: y => y ey Hey Hty.
    move=> /= Hne.
    dependent destruction Htx.
    dependent destruction Hty.
    rewrite /=.
    apply: (lidx_disjoint Hex Hey).
    assumption.
  Qed.

  (* Create a new variable. *)

  Definition new_var (E : t) : var := VM.new_var (vmap E).

  Lemma new_var_is_new :
    forall (E : t), ~~ mem (new_var E) E.
  Proof.
    move=> E.
    exact: (VM.new_var_is_new (vmap E)).
  Qed.

  (* Convert to SEnv. *)

  Definition to_senv (E : t) : SEnv.t := VM.vset (vmap E).

  Lemma mem_to_senv E :
    forall x, mem x E -> SEnv.mem x (to_senv E).
  Proof.
    exact: VM.mem_vset.
  Qed.

  (* Convert to TEnv. *)

  Definition to_tenv (E : t) : TEnv.t T :=
    VM.map (vty (types:=vtypes E)) (vmap E).

  Lemma mem_to_tenv E :
    forall x, mem x E -> TEnv.mem x (to_tenv E).
  Proof.
    rewrite /TEnv.mem /to_tenv => x Hmem.
    rewrite VM.Lemmas.map_b.
    exact: Hmem.
  Qed.

  Lemma to_tenv_find_ty (E : t) :
    forall x, find_type x E = TEnv.find x (to_tenv E).
  Proof.
    rewrite /find_type /find /TEnv.find /to_tenv => x.
    case H: (VM.find x (vmap E)).
    - apply: Logic.eq_sym.
      exact: (VM.Lemmas.find_some_map _ H).
    - apply: Logic.eq_sym.
      exact: (VM.Lemmas.find_none_map _ H).
  Qed.

  End Env.

End HEnv.
