
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype.
From Common Require Import Types Lists FSets Bools ZAriths Var Store.
From mQhasm Require Import zDSL.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Delimit Scope zssa_scope with zssa.

Local Open Scope zssa_scope.

Module MakeZSSA (VO : SsrOrderedType) (IO : SsrOrderedType).
  Module V := MakeSsrPairOrderedType VO IO.
  Module Q := MakeZDSL V.
  Include Q.
End MakeZSSA.

Module zSSA := MakeZSSA VarOrder NOrder.

Arguments zSSA.zVar v%N.

Notation "@- x" := (zSSA.zNeg x) (at level 35, right associativity) : zssa_scope.
Notation "x @+ y" := (zSSA.zBinop zSSA.zAdd x y) (at level 50, left associativity) : zssa_scope.
Notation "x @- y" := (zSSA.zBinop zSSA.zSub x y)  (at level 50, left associativity) : zssa_scope.
Notation "x @* y" := (zSSA.zBinop zSSA.zMul x y)  (at level 40, left associativity) : zssa_scope.
Notation "x @^ y" := (zSSA.zPow x y)  (at level 30, right associativity) : zssa_scope.
Notation "x @:= y" := (zSSA.zAssign x y) (at level 70, no associativity) : zssa_scope.
Notation "[ x , y ] @:= z # p" := (zSSA.zSplit x y z p) (at level 0, format "[ x , y ] @:= z # p", only parsing) : zssa_scope.
Notation "x @= y" := (zSSA.zEq x y) (at level 70, no associativity) : zssa_scope.
Notation "x @= y 'mod' z" := (zSSA.zEqMod x y z) (at level 70, y at next level, no associativity) : zssa_scope.
Notation "x @&& y" := (zSSA.zAnd x y) (at level 70, no associativity) : zssa_scope.
Notation "s |= f" := (zSSA.eval_bexp f true s) (at level 74, no associativity) : zssa_scope.
Notation "f ===> g" := (zSSA.entails f g) (at level 82, no associativity) : zssa_scope.
Notation "{{ f }} p {{ g }}" := ({| zSSA.spre := f; zSSA.sprog := p; zSSA.spost := g |}) (at level 82, no associativity) : zssa_scope.
Notation "|= s" := (zSSA.valid_spec s) (at level 83, no associativity) : zssa_scope.

Definition svar (x : zSSA.V.t) := fst x.
Definition sidx (x : zSSA.V.t) := snd x.
Hint Unfold svar sidx.

Module M2 := Map2 VS zSSA.VS.



Open Scope N_scope.

(** Conversion to SSA *)

Definition index : Type := N.

(* A map from a DSL variable to its current index. *)
Definition vmap : Type := VM.t index.

Definition empty_vmap : vmap := VM.empty index.

Definition initial_index : index := 0.

Definition first_assigned_index : index := 1.

(* Find the current index of a DSL variable. *)
Definition get_index (v : var) (m : vmap) : index :=
  match VM.find v m with
  | None => initial_index
  | Some i => i
  end.

(* Increment the current index of a DSL variable. *)
Definition upd_index (v : var) (m : vmap) : vmap :=
  match VM.find v m with
  | None => VM.add v first_assigned_index m
  | Some i => VM.add v (i + 1) m
  end.

Definition ssa_var (m : vmap) (v : var) : zSSA.var := (v, get_index v m).

Lemma ssa_var_preserve m : M2.preserve (ssa_var m).
Proof.
  move=> x y H.
  rewrite (eqP H).
  exact: eqxx.
Qed.

Lemma ssa_var_injective m : M2.injective (ssa_var m).
Proof.
  move=> x y /eqP H.
  case: H => H _.
  rewrite H; exact: eqxx.
Qed.

Definition ssa_var_well m :=
  M2.mkWellMap2 (ssa_var_preserve m) (ssa_var_injective (m:=m)).

Definition ssa_vars (m : vmap) (vs : VS.t) : zSSA.VS.t :=
  M2.map2 (ssa_var m) vs.

Definition ssa_unop (op : unop) : zSSA.unop :=
  match op with
  | zNeg => zSSA.zNeg
  end.

Definition ssa_binop (op : binop) : zSSA.binop :=
  match op with
  | zAdd => zSSA.zAdd
  | zSub => zSSA.zSub
  | zMul => zSSA.zMul
  end.

Fixpoint ssa_exp (m : vmap) (e : exp) : zSSA.exp :=
  match e with
  | zVar v => zSSA.zVar (ssa_var m v)
  | zConst c => zSSA.zConst c
  | zUnop op e => zSSA.zUnop (ssa_unop op) (ssa_exp m e)
  | zBinop op e1 e2 => zSSA.zBinop (ssa_binop op) (ssa_exp m e1) (ssa_exp m e2)
  | zPow e n => zSSA.zPow (ssa_exp m e) n
  end.

Definition ssa_instr (m : vmap) (i : instr) : vmap * zSSA.instr :=
  match i with
  | zAssign v e =>
    let e := ssa_exp m e in
    let m := upd_index v m in
    (m, zSSA.zAssign (ssa_var m v) e)
  | zSplit vh vl e p =>
    let e := ssa_exp m e in
    let mh := upd_index vh m in
    let ml := upd_index vl mh in
    (ml, zSSA.zSplit (ssa_var mh vh) (ssa_var ml vl) e p)
  end.

Fixpoint ssa_program (m : vmap) (p : program) : (vmap * zSSA.program) :=
  match p with
  | [::] => (m, [::])
  | hd::tl =>
    let (m, hd) := ssa_instr m hd in
    let (m, tl) := ssa_program m tl in
    (m, hd::tl)
  end.

Fixpoint ssa_bexp (m : vmap) (e : bexp) : zSSA.bexp :=
  match e with
  | zTrue => zSSA.zTrue
  | zEq e1 e2 => zSSA.zEq (ssa_exp m e1) (ssa_exp m e2)
  | zEqMod e1 e2 p => zSSA.zEqMod (ssa_exp m e1) (ssa_exp m e2) p
  | zAnd e1 e2 => zSSA.zAnd (ssa_bexp m e1) (ssa_bexp m e2)
  end.

Definition ssa_spec (s : spec) : zSSA.spec :=
  let m := empty_vmap in
  let f := ssa_bexp m (spre s) in
  let (m, p) := ssa_program m (sprog s) in
  let g := ssa_bexp m (spost s) in
  {| zSSA.spre := f; zSSA.sprog := p; zSSA.spost := g |}.

Lemma ssa_zassign :
  forall m1 m2 v e si,
    ssa_instr m1 (zAssign v e) = (m2, si) ->
    m2 = upd_index v m1 /\ si = zSSA.zAssign (ssa_var m2 v) (ssa_exp m1 e).
Proof.
  move=> m1 m2 v e si /= [Hm Hsi].
  split.
  - by symmetry.
  - rewrite Hm in Hsi.
    by symmetry.
Qed.

Lemma ssa_zsplit :
  forall m1 m2 vh vl e p si,
    ssa_instr m1 (zSplit vh vl e p) = (m2, si) ->
    m2 = upd_index vl (upd_index vh m1) /\
    si = zSSA.zSplit (ssa_var (upd_index vh m1) vh) (ssa_var m2 vl) (ssa_exp m1 e) p.
Proof.
  move=> m1 m2 vh vl e p si /= [Hm Hsi].
  split.
  - by symmetry.
  - rewrite Hm in Hsi.
    by symmetry.
Qed.

Lemma ssa_program_empty : forall m, ssa_program m [::] = (m, [::]).
Proof.
  reflexivity.
Qed.

Lemma ssa_program_cons :
  forall m1 m2 hd tl p,
    ssa_program m1 (hd::tl) = (m2, p) ->
    exists m3 h t,
      ssa_instr m1 hd = (m3, h) /\ ssa_program m3 tl = (m2, t) /\ p = h::t.
Proof.
  move=> m1 m2 hd tl p /=.
  set tmp := ssa_instr m1 hd.
  have: (tmp = ssa_instr m1 hd) by reflexivity.
  destruct tmp as [m3 h].
  set tmp := ssa_program m3 tl.
  have: (tmp = ssa_program m3 tl) by reflexivity.
  destruct tmp as [m4 t].
  move=> Htl Hhd [] Hm Hp.
  exists m3; exists h; exists t; split; [idtac | split].
  - reflexivity.
  - rewrite -Htl Hm.
    reflexivity.
  - symmetry; exact: Hp.
Qed.

Lemma ssa_spec_unfold s :
  exists m, zSSA.spre (ssa_spec s) = ssa_bexp empty_vmap (spre s) /\
            (m, zSSA.sprog (ssa_spec s)) = ssa_program empty_vmap (sprog s) /\
            zSSA.spost (ssa_spec s) = ssa_bexp m (spost s).
Proof.
  destruct s as [f p g] => /=.
  rewrite /ssa_spec /=.
  set tmp := ssa_program empty_vmap p.
  destruct tmp as [m sp] => /=.
  exists m; split; [idtac | split]; reflexivity.
Qed.

Lemma get_index_empty v :
  get_index v empty_vmap = 0.
Proof.
  done.
Qed.

Lemma get_index_add_eq x y i s :
  x == y ->
  get_index x (VM.add y i s) = i.
Proof.
  move=> Heq.
  rewrite (eqP Heq) /get_index (VM.Lemmas.find_add_eq _ _ (eqxx y)).
  reflexivity.
Qed.

Lemma get_index_add_neq x y i s :
  x != y ->
  get_index x (VM.add y i s) = get_index x s.
Proof.
  move=> /negP Hne.
  rewrite /get_index (VM.Lemmas.find_add_neq _ _ Hne).
  reflexivity.
Qed.

Lemma get_upd_index_gt0 :
  forall (m : vmap) (v : var),
    0 <? get_index v (upd_index v m).
Proof.
  move=> m v; rewrite /upd_index.
  case: (VM.find v m) => /=.
  - move=> a.
    rewrite (get_index_add_eq _ _ (eqxx v)).
    exact: Nltn0Sn.
  - rewrite (get_index_add_eq _ _ (eqxx v)).
    done.
Qed.

Lemma get_upd_index_lt :
  forall (m : vmap) (v : var),
    get_index v m <? get_index v (upd_index v m).
Proof.
  move=> m v; rewrite /upd_index /get_index.
  case: (VM.find v m) => /=.
  - move=> a.
    rewrite (VM.Lemmas.find_add_eq _ _ (eqxx v)).
    exact: NltnSn.
  - rewrite (VM.Lemmas.find_add_eq _ _ (eqxx v)).
    done.
Qed.

Lemma get_upd_index_leF :
  forall (m : vmap) (v : var),
    get_index v (upd_index v m) <=? get_index v m -> False.
Proof.
  move=> m v Hle.
  move: (get_upd_index_lt m v) => Hlt.
  move: (Nleq_ltn_trans Hle Hlt).
  rewrite Nltnn.
  done.
Qed.

Lemma get_upd_index_eq :
  forall (m : vmap) (v : var),
    get_index v (upd_index v m) = get_index v m + 1.
Proof.
  move=> m v.
  rewrite /upd_index.
  case H: (VM.find v m).
  - rewrite /get_index.
    rewrite (VM.Lemmas.find_add_eq m _ (eqxx v)).
    rewrite H.
    reflexivity.
  - rewrite /get_index.
    rewrite (VM.Lemmas.find_add_eq m _ (eqxx v)).
    rewrite H.
    reflexivity.
Qed.

Lemma get_upd_index_neq :
  forall (m : vmap) (x v : var),
    x != v ->
    get_index x (upd_index v m) = get_index x m.
Proof.
  move=> m x v => /negP Hne.
  rewrite /upd_index /get_index.
  case: (VM.find v m).
  - move=> a.
    rewrite (VM.Lemmas.find_add_neq _ _ Hne).
    reflexivity.
  - rewrite (VM.Lemmas.find_add_neq _ _ Hne).
    reflexivity.
Qed.

Lemma get_upd_index_le :
  forall (m : vmap) (x v : var),
    get_index x m <=? get_index x (upd_index v m).
Proof.
  move=> m x v.
  case Hxv: (x == v).
  - move: (get_upd_index_lt m v) => Hlt.
    rewrite (eqP Hxv).
    exact: (NltnW Hlt).
  - move/idP/negP: Hxv => Hxv.
    rewrite (get_upd_index_neq _ Hxv).
    exact: Nleqnn.
Qed.

Lemma ssa_instr_index_le :
  forall m1 m2 v i si,
    ssa_instr m1 i = (m2, si) ->
    get_index v m1 <=? get_index v m2.
Proof.
  move=> m1 m2 v i si.
  elim: i m1 m2 v si.
  - move=> v e m1 m2 x si Hsi.
    move: (ssa_zassign Hsi) => {Hsi} [Hupd Hsi].
    rewrite Hupd.
    exact: get_upd_index_le.
  - move=> vh vl e p m1 m2 x si Hsi.
    move: (ssa_zsplit Hsi) => {Hsi} [Hupd Hsi].
    rewrite Hupd.
    move: (get_upd_index_le m1 x vh) => Hle1.
    move: (get_upd_index_le (upd_index vh m1) x vl) => Hle2.
    exact: (Nleq_trans Hle1 Hle2).
Qed.

Lemma ssa_program_index_le :
  forall m1 m2 v p sp,
    ssa_program m1 p = (m2, sp) ->
    get_index v m1 <=? get_index v m2.
Proof.
  move=> m1 m2 v p sp.
  elim: p m1 m2 v sp.
  - move=> m1 m2 v sp Hsp.
    rewrite ssa_program_empty in Hsp.
    case: Hsp => Hm1 Hsp.
    rewrite Hm1; exact: Nleqnn.
  - move=> hd tl IH m1 m2 v sp Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    move: (ssa_instr_index_le v Hshd) => Hle1.
    move: (IH _ _ v _ Hstl) => Hle2.
    exact: (Nleq_trans Hle1 Hle2).
Qed.

Lemma ssa_eval_unop :
  forall (op : unop) (v : value),
    zSSA.eval_unop (ssa_unop op) v = eval_unop op v.
Proof.
  by case.
Qed.

Lemma ssa_eval_binop :
  forall (op : binop) (v1 v2 : value),
    zSSA.eval_binop (ssa_binop op) v1 v2 = eval_binop op v1 v2.
Proof.
  by case.
Qed.

Lemma ssa_var_upd_eq v m :
  ssa_var (upd_index v m) v = (v, get_index v (upd_index v m)).
Proof.
  reflexivity.
Qed.

Lemma ssa_var_upd_neq x v m :
  x != v ->
  ssa_var (upd_index v m) x = ssa_var m x.
Proof.
  move=> Hxv.
  rewrite /ssa_var.
  rewrite (get_upd_index_neq _ Hxv).
  reflexivity.
Qed.

Lemma ssa_vars_mem_elements m v vs :
  zSSA.VS.mem v (ssa_vars m vs) = (v \in (zSSA.VS.elements (ssa_vars m vs))).
Proof.
  move: (zSSA.VSLemmas.F.elements_iff (ssa_vars m vs) v) => [HinA Hin].
  case Hv: (v \in zSSA.VS.elements (ssa_vars m vs)).
  - move/InAP: Hv => Hv.
    apply/zSSA.VSLemmas.memP.
    apply: Hin.
    assumption.
  - move/negP: Hv => Hv.
    apply/negP => /zSSA.VSLemmas.memP Hmem.
    apply: Hv.
    apply/InAP.
    apply: HinA.
    assumption.
Qed.

Lemma ssa_vars_Empty m vs :
  VS.Empty vs ->
  zSSA.VS.Empty (ssa_vars m vs).
Proof.
  exact: M2.map2_Empty1.
Qed.

Lemma ssa_vars_mem1 m v vs :
  zSSA.VS.mem (ssa_var m v) (ssa_vars m vs) = VS.mem v vs.
Proof.
  exact: (M2.map2_mem1 (ssa_var_well m)).
Qed.

Lemma ssa_vars_mem2 m v vs :
  zSSA.VS.mem v (ssa_vars m vs) ->
  exists x, v = ssa_var m x /\ VS.mem x vs.
Proof.
  move=> Hmem; move: (M2.map2_mem2 Hmem) => [y [/eqP Hy Hmemy]].
  rewrite Hy.
  by exists y.
Qed.

Lemma ssa_vars_mem3 m v i vs :
  VS.mem v vs ->
  i = get_index v m ->
  zSSA.VS.mem (v, i) (ssa_vars m vs).
Proof.
  move=> Hmem Hidx.
  rewrite Hidx.
  rewrite ssa_vars_mem1.
  assumption.
Qed.

Lemma ssa_vars_mem_2vmap m1 m2 v vs :
  zSSA.VS.mem (ssa_var m1 v) (ssa_vars m2 vs) = VS.mem v vs && (get_index v m1 == get_index v m2).
Proof.
  case Hmem: (VS.mem v vs) => /=.
  - case Hidx: (get_index v m1 == get_index v m2) => /=.
    + rewrite /ssa_var (eqP Hidx) ssa_vars_mem1.
      assumption.
    + apply/negP => H.
      move/negP: Hidx; apply.
      move: (ssa_vars_mem2 H) => [y [[Hvy /eqP Hidx] Hy]].
      rewrite {2}Hvy; assumption.
  - apply/negP => H.
    move/negP: Hmem; apply.
    move: (ssa_vars_mem2 H) => [y [[Hvy _] Hy]].
    rewrite Hvy; assumption.
Qed.

Lemma ssa_vars_add m v vs :
  zSSA.VS.Equal (ssa_vars m (VS.add v vs))
               (zSSA.VS.add (ssa_var m v) (ssa_vars m vs)).
Proof.
  rewrite /ssa_vars (M2.map2_add (ssa_var_well m)).
  reflexivity.
Qed.

Lemma ssa_vars_upd_mem1 m x v vs :
  zSSA.VS.mem x (ssa_vars (upd_index v m) vs) ->
  x == ssa_var (upd_index v m) v \/
  svar x != v /\ zSSA.VS.mem x (ssa_vars m vs).
Proof.
  move=> Hmem.
  move: (ssa_vars_mem2 Hmem) => [y [Hxy Hy]].
  rewrite Hxy.
  case Hyv: (y == v).
  - left; rewrite (eqP Hyv); exact: eqxx.
  - right; split; first by done.
    move/idP/negP: Hyv => Hyv.
    rewrite (ssa_var_upd_neq _ Hyv) ssa_vars_mem1.
    assumption.
Qed.

Lemma ssa_vars_upd_mem2 m x v vs :
  x == ssa_var (upd_index v m) v ->
  VS.mem v vs ->
  zSSA.VS.mem x (ssa_vars (upd_index v m) vs).
Proof.
  move=> /eqP Heq Hmem.
  rewrite Heq ssa_vars_mem1.
  assumption.
Qed.

Lemma ssa_vars_upd_mem3 m x v vs :
  svar x != v ->
  zSSA.VS.mem x (ssa_vars m vs) ->
  zSSA.VS.mem x (ssa_vars (upd_index v m) vs).
Proof.
  destruct x as [x i] => /=.
  move=> Hneq Hmem.
  move: (ssa_vars_mem2 Hmem) => [y [Hxy Hmemy]].
  rewrite Hxy.
  rewrite ssa_vars_mem_2vmap.
  apply/andP; split.
  - assumption.
  - case: Hxy => [Hxy Hidx].
    rewrite Hxy in Hneq.
    rewrite (get_upd_index_neq _ Hneq).
    exact: eqxx.
Qed.

Lemma ssa_vars_union m vs1 vs2 :
  zSSA.VS.Equal (ssa_vars m (VS.union vs1 vs2))
               (zSSA.VS.union (ssa_vars m vs1) (ssa_vars m vs2)).
Proof.
  rewrite /ssa_vars (M2.map2_union (ssa_var_well m)).
  reflexivity.
Qed.

Lemma ssa_vars_exp_comm m e :
  zSSA.VS.Equal (ssa_vars m (vars_exp e)) (zSSA.vars_exp (ssa_exp m e)).
Proof.
  elim: e => /=.
  - move=> v.
    rewrite /ssa_vars (M2.map2_singleton (ssa_var_well m)).
    reflexivity.
  - move=> _ x; split => H; by inversion H.
  - move=> _ e IH.
    assumption.
  - move=> _ e1 IH1 e2 IH2.
    rewrite -IH1 -IH2 ssa_vars_union.
    reflexivity.
  - move=> e IH _.
    assumption.
Qed.

Lemma ssa_vars_exp_union m e1 e2 :
 zSSA.VS.Equal (ssa_vars m (VS.union (vars_exp e1) (vars_exp e2)))
              (zSSA.VS.union (zSSA.vars_exp (ssa_exp m e1))
                            (zSSA.vars_exp (ssa_exp m e2))).
Proof.
  rewrite ssa_vars_union -2!ssa_vars_exp_comm.
  reflexivity.
Qed.

Lemma ssa_vars_subset m s1 s2 :
  zSSA.VS.subset (ssa_vars m s1) (ssa_vars m s2) = VS.subset s1 s2.
Proof.
  case Hsub: (VS.subset s1 s2).
  - apply: zSSA.VS.subset_1 => x /zSSA.VSLemmas.memP Hmem.
    apply/zSSA.VSLemmas.memP.
    move: (ssa_vars_mem2 Hmem) => [y [Hxy Hmemy]].
    rewrite Hxy ssa_vars_mem1.
    exact: (VSLemmas.mem_subset Hmemy Hsub).
  - apply/negP => H.
    move/negP: Hsub; apply.
  - apply: VS.subset_1 => x /VSLemmas.memP Hmem.
    apply/VSLemmas.memP.
    rewrite -2!(ssa_vars_mem1 m) in Hmem *.
    exact: (zSSA.VSLemmas.mem_subset Hmem H).
Qed.

Lemma ssa_vars_bexp_comm m e :
  zSSA.VS.Equal (ssa_vars m (vars_bexp e)) (zSSA.vars_bexp (ssa_bexp m e)).
Proof.
  elim: e => /=.
  - move=> x; split => H; by inversion H.
  - move=> e1 e2.
    rewrite ssa_vars_exp_union.
    reflexivity.
  - move=> e1 e2 _.
    rewrite ssa_vars_exp_union.
    reflexivity.
  - move=> e1 IH1 e2 IH2.
    rewrite -IH1 -IH2 ssa_vars_union.
    reflexivity.
Qed.

Lemma ssa_vars_bexp_union m e1 e2 :
 zSSA.VS.Equal (ssa_vars m (VS.union (vars_bexp e1) (vars_bexp e2)))
              (zSSA.VS.union (zSSA.vars_bexp (ssa_bexp m e1))
                            (zSSA.vars_bexp (ssa_bexp m e2))).
Proof.
  rewrite ssa_vars_union -2!ssa_vars_bexp_comm.
  reflexivity.
Qed.

Lemma ssa_vars_exp_subset m e vs :
  zSSA.VS.subset (zSSA.vars_exp (ssa_exp m e)) (ssa_vars m vs) =
  VS.subset (vars_exp e) vs.
Proof.
  case Hsub: (VS.subset (vars_exp e) vs).
  - apply: zSSA.VS.subset_1 => x.
    rewrite -ssa_vars_exp_comm => /zSSA.VSLemmas.memP Hx.
    move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
    apply/zSSA.VSLemmas.memP.
    rewrite Hv ssa_vars_mem1.
    exact: (VSLemmas.mem_subset Hmemv Hsub).
  - move/negP : Hsub => H.
    apply/negP => Hsub; apply: H.
    apply/VS.subset_1 => x /VSLemmas.memP Hx.
    move: Hx.
    rewrite -(ssa_vars_mem1 m) ssa_vars_exp_comm => Hx.
    apply/VSLemmas.memP.
    move: (zSSA.VSLemmas.mem_subset Hx Hsub) => Hmem.
    rewrite ssa_vars_mem1 in Hmem.
    assumption.
Qed.

Lemma ssa_vars_bexp_subset m e vs :
  zSSA.VS.subset (zSSA.vars_bexp (ssa_bexp m e)) (ssa_vars m vs) =
  VS.subset (vars_bexp e) vs.
Proof.
  case Hsub: (VS.subset (vars_bexp e) vs).
  - apply: zSSA.VS.subset_1 => x.
    rewrite -ssa_vars_bexp_comm => /zSSA.VSLemmas.memP Hx.
    move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
    apply/zSSA.VSLemmas.memP.
    rewrite Hv ssa_vars_mem1.
    exact: (VSLemmas.mem_subset Hmemv Hsub).
  - move/negP : Hsub => H.
    apply/negP => Hsub; apply: H.
    apply/VS.subset_1 => x /VSLemmas.memP Hx.
    move: Hx.
    rewrite -(ssa_vars_mem1 m) ssa_vars_bexp_comm => Hx.
    apply/VSLemmas.memP.
    move: (zSSA.VSLemmas.mem_subset Hx Hsub) => Hmem.
    rewrite ssa_vars_mem1 in Hmem.
    assumption.
Qed.

Lemma ssa_vars_upd_index_subset1 m v vs :
  zSSA.VS.subset (ssa_vars (upd_index v m) vs)
                (zSSA.VS.add (ssa_var (upd_index v m) v) (ssa_vars m vs)).
Proof.
  apply: zSSA.VS.subset_1 => x /zSSA.VSLemmas.memP Hmem.
  apply/zSSA.VSLemmas.memP.
  move: (ssa_vars_mem2 Hmem) => [y [Hxy Hy]].
  rewrite Hxy.
  case Hyv: (y == v).
  - apply: zSSA.VSLemmas.mem_add2.
    rewrite (eqP Hyv).
    exact: eqxx.
  - apply: zSSA.VSLemmas.mem_add3.
    rewrite ssa_vars_mem_2vmap.
    apply/andP; split.
    + assumption.
    + move/idP/negP: Hyv => Hyv.
      rewrite (get_upd_index_neq _ Hyv).
      exact: eqxx.
Qed.

Lemma ssa_vars_upd_index_subset2 m vh vl vs :
  zSSA.VS.subset (ssa_vars (upd_index vl (upd_index vh m)) vs)
                (zSSA.VS.add (ssa_var (upd_index vh m) vh) (zSSA.VS.add (ssa_var (upd_index vl (upd_index vh m)) vl) (ssa_vars m vs))).
Proof.
  apply: zSSA.VS.subset_1 => x /zSSA.VSLemmas.memP Hmem.
  apply/zSSA.VSLemmas.memP.
  move: (ssa_vars_mem2 Hmem) => [y [Hxy Hy]].
  rewrite Hxy.
  case Hyvl: (y == vl).
  - apply: zSSA.VSLemmas.mem_add3.
    apply: zSSA.VSLemmas.mem_add2.
    rewrite (eqP Hyvl).
    exact: eqxx.
  - move/idP/negP: Hyvl => Hyvl.
    rewrite (ssa_var_upd_neq _ Hyvl).
    case Hyvh: (y == vh).
    + apply: zSSA.VSLemmas.mem_add2.
      rewrite (eqP Hyvh).
      exact: eqxx.
    + move/idP/negP: Hyvh => Hyvh.
      rewrite (ssa_var_upd_neq _ Hyvh).
      apply: zSSA.VSLemmas.mem_add3.
      apply: zSSA.VSLemmas.mem_add3.
      rewrite ssa_vars_mem1.
      assumption.
Qed.

Lemma ssa_vars_instr_subset vs m1 m2 i si :
  ssa_instr m1 i = (m2, si) ->
  zSSA.VS.subset (ssa_vars m2 (VS.union vs (vars_instr i)))
                (zSSA.VS.union (ssa_vars m1 vs) (zSSA.vars_instr si)).
Proof.
  elim: i vs m1 m2 si => /=.
  - move=> v e vs m1 m2 si [] Hm Hsi.
    rewrite -Hsi -Hm /= => {Hm Hsi si m2}.
    move: (ssa_vars_upd_index_subset1 m1 v vs) => Hsub1.
    move: (ssa_vars_upd_index_subset1 m1 v (vars_exp e)) => Hsub2.
    have: zSSA.VS.mem (ssa_var (upd_index v m1) v) (zSSA.VS.add (ssa_var (upd_index v m1) v) (ssa_vars m1 vs)) by apply: zSSA.VSLemmas.mem_add2; exact: eqxx.
    move=> Hmem.
    move: (zSSA.VSLemmas.subset_add3 Hmem Hsub1) => {Hmem Hsub1} Hsub1.
    move: (zSSA.VSLemmas.union_subsets Hsub1 Hsub2) => {Hsub1 Hsub2}.
    set m2 := upd_index v m1.
    rewrite -{1}ssa_vars_add -{1}ssa_vars_union => Hsub.
    have: zSSA.VS.subset (ssa_vars m2 (VS.union vs (VS.add v (vars_exp e))))
                        (ssa_vars m2 (VS.union (VS.add v vs) (vars_exp e))).
    + rewrite ssa_vars_subset VSLemmas.OP.P.union_sym VSLemmas.OP.P.union_add
              VSLemmas.OP.P.union_sym -VSLemmas.OP.P.union_add.
      exact: VSLemmas.subset_refl.
    + move=> Hsub1.
      move: (zSSA.VSLemmas.subset_trans Hsub1 Hsub) => {Hsub1 Hsub} Hsub.
      have: zSSA.VS.subset (zSSA.VS.union (zSSA.VS.add (ssa_var m2 v) (ssa_vars m1 vs))
                                        (zSSA.VS.add (ssa_var m2 v) (ssa_vars m1 (vars_exp e))))
                          (zSSA.VS.union (ssa_vars m1 vs)
                                        (zSSA.VS.add (ssa_var m2 v) (zSSA.vars_exp (ssa_exp m1 e)))).
      * rewrite zSSA.VSLemmas.OP.P.union_add.
        apply: zSSA.VSLemmas.subset_add3.
        -- apply: zSSA.VSLemmas.mem_union3.
           apply: zSSA.VSLemmas.mem_add2.
           exact: eqxx.
        -- rewrite ssa_vars_exp_comm.
           exact: zSSA.VSLemmas.subset_refl.
      * move=> Hsub2.
        move: (zSSA.VSLemmas.subset_trans Hsub Hsub2) => {Hsub Hsub2} Hsub.
        assumption.
  - move=> vh vl e p vs m1 m2 si [] Hm Hsi.
    rewrite -Hsi -Hm /= => {Hm Hsi si m2}.
    move: (ssa_vars_upd_index_subset2 m1 vh vl vs) => Hsub1.
    move: (ssa_vars_upd_index_subset2 m1 vh vl (vars_exp e)) => Hsub2.
    have: zSSA.VS.mem (ssa_var (upd_index vl (upd_index vh m1)) vh) (zSSA.VS.add (ssa_var (upd_index vh m1) vh) (zSSA.VS.add (ssa_var (upd_index vl (upd_index vh m1)) vl) (ssa_vars m1 vs))).
      case Hhl: (vh == vl).
      rewrite (eqP Hhl).
      apply: zSSA.VSLemmas.mem_add3; apply: zSSA.VSLemmas.mem_add2; exact: eqxx.
      move/idP/negP: Hhl => Hhl.
      rewrite (ssa_var_upd_neq _ Hhl).
      apply: zSSA.VSLemmas.mem_add2; exact: eqxx.
    have: zSSA.VS.mem (ssa_var (upd_index vl (upd_index vh m1)) vl) (zSSA.VS.add (ssa_var (upd_index vh m1) vh) (zSSA.VS.add (ssa_var (upd_index vl (upd_index vh m1)) vl) (ssa_vars m1 vs))) by apply: zSSA.VSLemmas.mem_add3; apply: zSSA.VSLemmas.mem_add2; exact: eqxx.
    move=> Hmemvl Hmemvh.
    move: (zSSA.VSLemmas.subset_add3 Hmemvl Hsub1) => {Hmemvl Hsub1} Hsub1.
    move: (zSSA.VSLemmas.subset_add3 Hmemvh Hsub1) => {Hmemvh Hsub1} Hsub1.
    move: (zSSA.VSLemmas.union_subsets Hsub1 Hsub2) => {Hsub1 Hsub2}.
    set m2 := upd_index vh m1.
    set m3 := upd_index vl m2.
    rewrite -2!{1}ssa_vars_add -{1}ssa_vars_union => Hsub.
    have: zSSA.VS.subset (zSSA.VS.union (zSSA.VS.add (ssa_var m2 vh) (zSSA.VS.add (ssa_var m3 vl) (ssa_vars m1 vs))) (zSSA.VS.add (ssa_var m2 vh) (zSSA.VS.add (ssa_var m3 vl) (ssa_vars m1 (vars_exp e)))))
                        (zSSA.VS.union (ssa_vars m1 vs) (zSSA.VS.add (ssa_var m2 vh) (zSSA.VS.add (ssa_var m3 vl) (zSSA.vars_exp (ssa_exp m1 e))))).
    + set vh2 := ssa_var m2 vh.
      set vl3 := ssa_var m3 vl.
      set vs1 := ssa_vars m1 vs.
      rewrite -ssa_vars_exp_comm.
      set e1 := ssa_vars m1 (vars_exp e).
      rewrite zSSA.VSLemmas.OP.P.union_add.
      have: zSSA.VS.mem vh2 (zSSA.VS.union vs1 (zSSA.VS.add vh2 (zSSA.VS.add vl3 e1))) by apply: zSSA.VSLemmas.mem_union3; apply: zSSA.VSLemmas.mem_add2; exact: eqxx.
      move=> Hmem; apply: (zSSA.VSLemmas.subset_add3 Hmem) => {Hmem}.
      rewrite zSSA.VSLemmas.OP.P.union_add.
      have: zSSA.VS.mem vl3 (zSSA.VS.union vs1 (zSSA.VS.add vh2 (zSSA.VS.add vl3 e1))) by apply: zSSA.VSLemmas.mem_union3; apply: zSSA.VSLemmas.mem_add3; apply: zSSA.VSLemmas.mem_add2; exact: eqxx.
      move=> Hmem; apply: (zSSA.VSLemmas.subset_add3 Hmem) => {Hmem}.
      exact: zSSA.VSLemmas.subset_refl.
    + move=> Hsub1.
      move: (zSSA.VSLemmas.subset_trans Hsub Hsub1) => {Hsub1 Hsub} Hsub.
      have: zSSA.VS.subset (ssa_vars m3 (VS.union vs (VS.add vh (VS.add vl (vars_exp e)))))
                          (ssa_vars m3 (VS.union (VS.add vh (VS.add vl vs)) (vars_exp e))).
      * rewrite ssa_vars_subset VSLemmas.OP.P.union_sym
                4!VSLemmas.OP.P.union_add VSLemmas.OP.P.union_sym.
        exact: VSLemmas.subset_refl.
      * move=> Hsub2.
        move: (zSSA.VSLemmas.subset_trans Hsub2 Hsub) => {Hsub Hsub2} Hsub.
        assumption.
Qed.

Lemma ssa_vars_post_subset vs m1 m2 p sp g :
  VS.subset (vars_bexp g) (VS.union vs (vars_program p)) ->
  ssa_program m1 p = (m2, sp) ->
  zSSA.VS.subset (zSSA.vars_bexp (ssa_bexp m2 g)) (zSSA.VS.union (ssa_vars m1 vs) (zSSA.vars_program sp)).
Proof.
  elim: p vs m1 m2 sp g => /=.
  - move=> vs m1 m2 sp g Hsub [] Hm Hsp.
    rewrite -Hsp -Hm /=.
    rewrite (zSSA.VSLemmas.OP.P.empty_union_2 _ zSSA.VS.empty_1).
    rewrite ssa_vars_bexp_subset.
    rewrite -(VSLemmas.OP.P.empty_union_2 vs VS.empty_1).
    assumption.
  - move=> hd tl IH vs m1 m2 sp g Hsub Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    rewrite Hsp /= => {Hsp}.
    move: Hsub; rewrite -VSLemmas.OP.P.union_assoc => Hsub.
    move: (IH _ _ _ _ _ Hsub Hstl) => {IH Hsub Hstl} H0.
    move: (zSSA.VS.subset_2 H0) => {H0} H0.
    move: (ssa_vars_instr_subset vs Hshd) => {Hshd} H1.
    move: (zSSA.VS.subset_2 H1) => {H1} H1.
    move: (zSSA.VSLemmas.OP.P.union_subset_4 (s'':=zSSA.vars_program stl) H1) => {H1} H1.
    rewrite -zSSA.VSLemmas.OP.P.union_assoc.
    move: (zSSA.VSLemmas.OP.P.subset_trans H0 H1) => {H0 H1} H2.
    apply: zSSA.VS.subset_1.
    assumption.
Qed.



(** State equivalence *)

Definition state_equiv (m : vmap) (s : State.t) (ss : zSSA.State.t) : Prop :=
  forall x, State.acc x s = zSSA.State.acc (x, get_index x m) ss.

Lemma pair_neq1 :
  forall (T : eqType) (a b c d : T),
    a != c -> (a, b) != (c, d).
Proof.
  move=> T a b c d Hne.
  apply/eqP => H.
  case: H => Hac Hbd.
  apply/idP: Hne.
  rewrite Hac; exact: eqxx.
Qed.

Lemma pair_neq2 :
  forall (T : eqType) (a b c d : T),
    b != d -> (a, b) != (c, d).
Proof.
  move=> T a b c d Hne.
  apply/eqP => H.
  case: H => Hac Hbd.
  apply/idP: Hne.
  rewrite Hbd; exact: eqxx.
Qed.

Lemma ssa_eval_exp m s ss e :
  state_equiv m s ss ->
  zSSA.eval_exp (ssa_exp m e) ss = eval_exp e s.
Proof.
  move=> Heq; elim: e => /=.
  - move=> v.
    rewrite (Heq v).
    reflexivity.
  - move=> c.
    reflexivity.
  - move=> op e IH.
    rewrite ssa_eval_unop IH.
    reflexivity.
  - move=> op e1 IH1 e2 IH2.
    rewrite ssa_eval_binop IH1 IH2.
    reflexivity.
  - move=> e IH p.
    rewrite IH.
    reflexivity.
Qed.

Lemma ssa_eval_bexp m s ss e :
  state_equiv m s ss ->
  zSSA.eval_bexp (ssa_bexp m e) ss <-> eval_bexp e s.
Proof.
  move=> Heq; elim: e => /=.
  - done.
  - move=> e1 e2.
    rewrite 2!(ssa_eval_exp _ Heq).
    done.
  - move=> e1 e2 p.
    rewrite 2!(ssa_eval_exp _ Heq).
    done.
  - move=> e1 [IH11 IH12] e2 [IH21 IH22].
    tauto.
Qed.

Lemma ssa_eval_bexp1 m s ss e :
  state_equiv m s ss ->
  zSSA.eval_bexp (ssa_bexp m e) ss -> eval_bexp e s.
Proof.
  move=> Heq He.
  move: (ssa_eval_bexp e Heq) => [H1 H2].
  exact: (H1 He).
Qed.

Lemma ssa_eval_bexp2 m s ss e :
  state_equiv m s ss ->
  eval_bexp e s -> zSSA.eval_bexp (ssa_bexp m e) ss.
Proof.
  move=> Heq He.
  move: (ssa_eval_bexp e Heq) => [H1 H2].
  exact: (H2 He).
Qed.

Lemma ssa_eval_instr :
  forall m1 m2 s1 s2 ss1 ss2 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    eval_instr s1 i = s2 ->
    zSSA.eval_instr ss1 si = ss2 ->
    state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 ss2 i.
  elim: i.
  - move=> v e si Hsi Heq /= Hei Hesi.
    move: (ssa_zassign Hsi) => {Hsi} [Hupd Hsi] x.
    rewrite Hsi /= in Hesi => {Hsi}.
    rewrite -Hei -Hesi => {Hei Hesi}.
    case Hxv: (x == v) => /=.
    + rewrite (State.acc_upd_eq _ _ Hxv).
      rewrite (eqP Hxv) (zSSA.State.acc_upd_eq _ _ (eqxx (ssa_var m2 v))).
      rewrite (ssa_eval_exp _ Heq).
      reflexivity.
    + move/idP/negP: Hxv => Hxv.
      rewrite (State.acc_upd_neq _ _ Hxv).
      rewrite (zSSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxv)).
      rewrite Hupd (get_upd_index_neq _ Hxv).
      exact: Heq.
  - move=> vh vl e p si Hsi Heq /= Hei Hesi.
    move: (ssa_zsplit Hsi) => {Hsi} [Hupd Hsi].
    rewrite Hsi /= in Hesi => {Hsi}.
    rewrite (ssa_eval_exp _ Heq) in Hesi.
    move: Hei Hesi; set tmp := Z.div_eucl (eval_exp e s1) (Z.pow_pos 2 p);
        destruct tmp as [q r] => Hei Hesi.
    move=> x.
    rewrite -Hei -Hesi => {Hei Hesi}.
    case Hxl: (x == vl); [idtac | case Hxh: (x == vh)].
    + rewrite (State.acc_upd_eq _ _ Hxl).
      rewrite (eqP Hxl) (zSSA.State.acc_upd_eq _ _ (eqxx (ssa_var m2 vl))).
      reflexivity.
    + move/idP/negP: Hxl => Hxl.
      rewrite (State.acc_upd_neq _ _ Hxl) (State.acc_upd_eq _ _ Hxh).
      rewrite (zSSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxl)).
      rewrite Hupd (get_upd_index_neq _ Hxl).
      rewrite (eqP Hxh) (zSSA.State.acc_upd_eq _ _ (eqxx (ssa_var (upd_index vh m1) vh))).
      reflexivity.
    + move/idP/negP: Hxl => Hxl.
      move/idP/negP: Hxh => Hxh.
      rewrite (State.acc_upd_neq _ _ Hxl) (State.acc_upd_neq _ _ Hxh).
      rewrite (zSSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxl))
              (zSSA.State.acc_upd_neq _ _ (pair_neq1 _ _ Hxh)).
      rewrite Hupd (get_upd_index_neq _ Hxl) (get_upd_index_neq _ Hxh).
      exact: Heq.
Qed.

Lemma ssa_eval_instr_succ :
  forall m1 m2 s1 s2 ss1 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    eval_instr s1 i = s2 ->
    exists ss2,
      zSSA.eval_instr ss1 si = ss2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 i si Hi Heq Hei.
  exists (zSSA.eval_instr ss1 si); split.
  - reflexivity.
  - exact: (ssa_eval_instr Hi Heq Hei).
Qed.

Lemma ssa_eval_program :
  forall m1 m2 s1 s2 ss1 ss2 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    eval_program s1 p = s2 ->
    zSSA.eval_program ss1 sp = ss2 ->
    state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 ss2 p.
  elim: p m1 m2 s1 s2 ss1 ss2 => /=.
  - move=> m1 m2 s1 s2 ss1 ss2 p [Hm Hp] Heq Hep Hesp.
    rewrite -Hp in Hesp.
    rewrite -Hep -Hesp -Hm.
    exact: Heq.
  - move=> hd tl IH m1 m2 s1 s2 ss1 ss2 sp Hsp Heq Hep Hesp.
    move: (eval_program_cons Hep) => {Hep} [s3 [Hehd Hetl]].
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [h [t [Hh [Ht Hht]]]]].
    rewrite Hht in Hesp.
    move: (zSSA.eval_program_cons Hesp) => [ss3 [Heshd Hestl]].
    move: (ssa_eval_instr Hh Heq Hehd Heshd) => Heq'.
    exact: (IH _ _ _ _ _ _ _ Ht Heq' Hetl Hestl).
Qed.

Lemma ssa_eval_program_succ :
  forall m1 m2 s1 s2 ss1 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    eval_program s1 p = s2 ->
    exists ss2,
      zSSA.eval_program ss1 sp = ss2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 s2 ss1 p sp Hp Heq Hep.
  exists (zSSA.eval_program ss1 sp); split.
  - reflexivity.
  - exact: (ssa_eval_program Hp Heq Hep).
Qed.

Lemma dessa_eval_instr_succ :
  forall m1 m2 s1 ss1 ss2 i si,
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    zSSA.eval_instr ss1 si = ss2 ->
    exists s2,
      eval_instr s1 i = s2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 ss1 ss2 i si Hi Heq Hesi.
  exists (eval_instr s1 i); split.
  - reflexivity.
  - apply: (ssa_eval_instr Hi Heq _ Hesi).
    reflexivity.
Qed.

Lemma dessa_eval_program_succ :
  forall m1 m2 s1 ss1 ss2 p sp,
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    zSSA.eval_program ss1 sp = ss2 ->
    exists s2,
      eval_program s1 p = s2 /\ state_equiv m2 s2 ss2.
Proof.
  move=> m1 m2 s1 ss1 ss2 p sp Hp Heq Hesp.
  exists (eval_program s1 p); split.
  - reflexivity.
  - apply: (ssa_eval_program Hp Heq _ Hesp).
    reflexivity.
Qed.



(** Convert a DSL state to an SSA state. *)

Definition ssa_state (m : vmap) (s : State.t) : zSSA.State.t :=
  fun v =>
    if (sidx v) == get_index (svar v) m
    then State.acc (svar v) s
    else State.acc (svar v) State.empty.

Lemma acc_ssa_state_eq :
  forall (m : vmap) (s : State.t) (v : var) (i : index),
    i == get_index v m ->
    zSSA.State.acc (v, i) (ssa_state m s) = State.acc v s.
Proof.
  move=> m s v i Heq.
  rewrite /ssa_state /zSSA.State.acc /zSSA.Store.acc /=.
  rewrite Heq.
  reflexivity.
Qed.

Lemma ssa_state_equiv :
  forall m s, state_equiv m s (ssa_state m s).
Proof.
  move=> m s x.
  rewrite (acc_ssa_state_eq _ (eqxx (get_index x m))).
  reflexivity.
Qed.



(** Convert an SSA state to a DSL state. *)

Definition dessa_state (m : vmap) (s : zSSA.State.t) : State.t :=
  fun v => zSSA.State.acc (v, get_index v m) s.

Lemma acc_dessa_state :
  forall (m : vmap) (s : zSSA.State.t) (v : var),
    State.acc v (dessa_state m s) = zSSA.State.acc (v, get_index v m) s.
Proof.
  reflexivity.
Qed.

Lemma ssa_dessaK :
  forall (m : vmap) (s : State.t) (x : var),
    State.acc x (dessa_state m (ssa_state m s)) = State.acc x s.
Proof.
  move=> m s x.
  rewrite acc_dessa_state.
  rewrite (acc_ssa_state_eq _ (eqxx (get_index x m))).
  reflexivity.
Qed.

Corollary dessa_state_equiv :
  forall m s, state_equiv m (dessa_state m s) s.
Proof.
  move=> m s x.
  exact: acc_dessa_state.
Qed.



(** Soundness and completeness *)

Theorem ssa_spec_sound (s : spec) :
  zSSA.valid_spec (ssa_spec s) -> valid_spec s.
Proof.
  destruct s as [f p g].
  rewrite /ssa_spec /=.
  set t := ssa_program empty_vmap p.
  have: (t = ssa_program empty_vmap p) by reflexivity.
  destruct t as [m ssa_p].
  move=> Hp Hspec s1 s2 /= Hf Hep.
  pose ss1 := ssa_state empty_vmap s1.
  pose Heq1 := (ssa_state_equiv empty_vmap s1).
  move: (ssa_eval_program_succ (Logic.eq_sym Hp) Heq1 Hep) => [ss2 [Hesp Heq2]].
  move: (ssa_eval_bexp2 Heq1 Hf) => Hsf.
  move: (Hspec ss1 ss2 Hsf Hesp) => /= Hsg.
  exact: (ssa_eval_bexp1 Heq2 Hsg).
Qed.

Theorem ssa_spec_complete (s : spec) :
  valid_spec s -> zSSA.valid_spec (ssa_spec s).
Proof.
  destruct s as [f p g].
  rewrite /ssa_spec /=.
  set t := ssa_program empty_vmap p.
  have: (t = ssa_program empty_vmap p) by reflexivity.
  destruct t as [m ssa_p].
  move=> Hp Hspec ss1 ss2 /= Hsf Hesp.
  pose s1 := dessa_state empty_vmap ss1.
  pose Heq1 := (dessa_state_equiv empty_vmap ss1).
  move: (dessa_eval_program_succ (Logic.eq_sym Hp) Heq1 Hesp) => [s2 [Hep Heq2]].
  move: (ssa_eval_bexp1 Heq1 Hsf) => Hf.
  move: (Hspec s1 s2 Hf Hep) => /= Hg.
  exact: (ssa_eval_bexp2 Heq2 Hg).
Qed.



(** Well-formed SSA *)

Definition ssa_var_unchanged_instr (v : zSSA.var) (i : zSSA.instr) : bool :=
  ~~ (zSSA.VS.mem v (zSSA.lvs_instr i)).

Definition ssa_unchanged_instr_var (i : zSSA.instr) (v : zSSA.var) : bool :=
  ~~ (zSSA.VS.mem v (zSSA.lvs_instr i)).

Definition ssa_vars_unchanged_instr (vs : zSSA.VS.t) (i : zSSA.instr) : bool :=
  zSSA.VS.for_all (ssa_unchanged_instr_var i) vs.

Definition ssa_var_unchanged_program (v : zSSA.var) (p : zSSA.program) : bool :=
  all (ssa_var_unchanged_instr v) p.

Definition ssa_unchanged_program_var (p : zSSA.program) (v : zSSA.var) : bool :=
  ssa_var_unchanged_program v p.

Definition ssa_vars_unchanged_program (vs : zSSA.VS.t) (p : zSSA.program) : bool :=
  zSSA.VS.for_all (ssa_unchanged_program_var p) vs.

Fixpoint ssa_single_assignment (p : zSSA.program) : bool :=
  match p with
  | [::] => true
  | hd::tl =>
    (ssa_vars_unchanged_program (zSSA.lvs_instr hd) tl) &&
    (ssa_single_assignment tl)
  end.

Definition well_formed_ssa_program (vs : zSSA.VS.t) (p : zSSA.program) : bool :=
  zSSA.well_formed_program vs p &&
  ssa_vars_unchanged_program vs p &&
  ssa_single_assignment p.

Definition well_formed_ssa_spec (vs : zSSA.VS.t) (s : zSSA.spec) : bool :=
  zSSA.well_formed_spec vs s &&
  ssa_vars_unchanged_program vs (zSSA.sprog s) &&
  ssa_single_assignment (zSSA.sprog s).

Lemma well_formed_ssa_spec_program vs s :
  well_formed_ssa_spec vs s ->
  well_formed_ssa_program vs (zSSA.sprog s).
Proof.
  move=> /andP [/andP [/andP [/andP [Hpre Hwell] Hprog] Hvs] Hssa].
  rewrite /well_formed_ssa_program Hwell Hvs Hssa.
  done.
Qed.

Lemma ssa_var_unchanged_zassign x v e :
  ssa_var_unchanged_instr x (v @:= e) ->
  x != v.
Proof.
  rewrite /ssa_var_unchanged_instr => /= Hi.
  apply/negP.
  exact: (zSSA.VSLemmas.not_mem_singleton1 Hi).
Qed.

Lemma ssa_var_unchanged_zsplit x vh vl e i :
  ssa_var_unchanged_instr x ([vh, vl] @:= e # i) ->
  (x != vh) && (x != vl).
Proof.
  rewrite /ssa_var_unchanged_instr => /= Hi.
  move: (zSSA.VSLemmas.not_mem_add1 Hi) => [Hm1 Hm2].
  apply/andP; split.
  - apply/negP; assumption.
  - apply/negP; exact: (zSSA.VSLemmas.not_mem_singleton1 Hm2).
Qed.

Lemma acc_unchanged_instr v i s1 s2 :
  ssa_var_unchanged_instr v i ->
  zSSA.eval_instr s1 i = s2 ->
  zSSA.State.acc v s1 = zSSA.State.acc v s2.
Proof.
  elim: i.
  - move=> v' e /= Hun Hei.
    move: (ssa_var_unchanged_zassign Hun) => {Hun} Hne.
    rewrite -Hei (zSSA.State.acc_upd_neq _ _ Hne).
    reflexivity.
  - move=> vh vl e p Hun Hei.
    move: (ssa_var_unchanged_zsplit Hun) => {Hun} /andP [Hneh Hnel].
    rewrite -Hei /= => {Hei}.
    set tmp := Z.div_eucl (zSSA.eval_exp e s1) (Z.pow_pos 2 p);
        destruct tmp as [q r].
    rewrite (zSSA.State.acc_upd_neq _ _ Hnel)
            (zSSA.State.acc_upd_neq _ _ Hneh).
    reflexivity.
Qed.

Lemma acc_unchanged_program v p s1 s2 :
  ssa_var_unchanged_program v p ->
  zSSA.eval_program s1 p = s2 ->
  zSSA.State.acc v s1 = zSSA.State.acc v s2.
Proof.
  elim: p s1 s2 => /=.
  - move=> s1 s2 _ Hep.
    rewrite Hep.
    reflexivity.
  - move=> hd tl IH s1 s2 /andP [Huchd Huctl] Hep.
    move: (zSSA.eval_program_cons Hep) => {Hep} [s3 [Hehd Hetl]].
    rewrite (acc_unchanged_instr Huchd Hehd).
    exact: (IH _ _ Huctl Hetl).
Qed.

Lemma ssa_var_unchanged_program_cons v hd tl :
  ssa_var_unchanged_program v (hd::tl) ->
  ssa_var_unchanged_instr v hd /\ ssa_var_unchanged_program v tl.
Proof.
  move => /andP H.
  exact: H.
Qed.

Lemma ssa_var_unchanged_program_concat v p1 p2 :
  ssa_var_unchanged_program v (p1 ++ p2) ->
  ssa_var_unchanged_program v p1 /\ ssa_var_unchanged_program v p2.
Proof.
  elim: p1 p2.
  - move=> /= p2 H.
    by rewrite H.
  - move=> hd tl IH p2 /andP [Hhd Htlp2].
    move: (IH _ Htlp2) => {IH Htlp2} [Htl Hp2].
    by rewrite /= Hhd Htl Hp2.
Qed.

Lemma acc_unchanged_program_cons v hd tl s1 s2 s3 :
  ssa_var_unchanged_program v (hd::tl) ->
  zSSA.eval_instr s1 hd = s2 ->
  zSSA.eval_program s2 tl = s3 ->
  zSSA.State.acc v s2 = zSSA.State.acc v s1 /\
  zSSA.State.acc v s3 = zSSA.State.acc v s1.
Proof.
  move=> /andP [Hunhd Huntl] Hehd Hetl.
  move: (acc_unchanged_instr Hunhd Hehd) (acc_unchanged_program Huntl Hetl) =>
    H21 H32.
  rewrite -H32 -H21.
  split; reflexivity.
Qed.

Lemma acc_unchanged_program_concat v p1 p2 s1 s2 s3 :
  ssa_var_unchanged_program v (p1 ++ p2) ->
  zSSA.eval_program s1 p1 = s2 ->
  zSSA.eval_program s2 p2 = s3 ->
  zSSA.State.acc v s2 = zSSA.State.acc v s1 /\
  zSSA.State.acc v s3 = zSSA.State.acc v s1.
Proof.
  move=> Hun12 Hep1 Hep2.
  move: (ssa_var_unchanged_program_concat Hun12) => {Hun12} [Hun1 Hun2].
  rewrite -(acc_unchanged_program Hun2 Hep2) -(acc_unchanged_program Hun1 Hep1).
  split; reflexivity.
Qed.

Lemma ssa_unchanged_instr_var_compat i :
  SetoidList.compat_bool zSSA.VS.E.eq (ssa_unchanged_instr_var i).
Proof.
  move=> x y Heq.
  rewrite (eqP Heq).
  reflexivity.
Qed.

Lemma ssa_unchanged_program_var_compat p :
  SetoidList.compat_bool zSSA.VS.E.eq (ssa_unchanged_program_var p).
Proof.
  move=> x y Heq.
  rewrite (eqP Heq).
  reflexivity.
Qed.

Lemma ssa_unchanged_instr_mem v vs i :
  ssa_vars_unchanged_instr vs i ->
  zSSA.VS.mem v vs ->
  ssa_var_unchanged_instr v i.
Proof.
  move=> Hun Hmem.
  apply: (zSSA.VS.for_all_2 (ssa_unchanged_instr_var_compat i) Hun).
  apply/zSSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_unchanged_program_mem v vs p :
  ssa_vars_unchanged_program vs p ->
  zSSA.VS.mem v vs ->
  ssa_var_unchanged_program v p.
Proof.
  move=> Hun Hmem.
  apply: (zSSA.VS.for_all_2 (ssa_unchanged_program_var_compat p) Hun).
  apply/zSSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_unchanged_instr_global vs i :
  (forall v, zSSA.VS.mem v vs -> ssa_var_unchanged_instr v i) ->
  ssa_vars_unchanged_instr vs i.
Proof.
  move=> H.
  apply: (zSSA.VS.for_all_1 (ssa_unchanged_instr_var_compat i)).
  move=> v Hin.
  apply: H; apply/zSSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_unchanged_program_global vs p :
  (forall v, zSSA.VS.mem v vs -> ssa_var_unchanged_program v p) ->
  ssa_vars_unchanged_program vs p.
Proof.
  move=> H.
  apply: (zSSA.VS.for_all_1 (ssa_unchanged_program_var_compat p)).
  move=> v Hin.
  apply: H; apply/zSSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_unchanged_instr_local vs i :
  ssa_vars_unchanged_instr vs i ->
  (forall v, zSSA.VS.mem v vs -> ssa_var_unchanged_instr v i).
Proof.
  move=> H v Hmem.
  apply: (zSSA.VS.for_all_2 (ssa_unchanged_instr_var_compat i) H).
  apply/zSSA.VSLemmas.memP; assumption.
Qed.

Lemma ssa_unchanged_program_local vs p :
  ssa_vars_unchanged_program vs p ->
  (forall v, zSSA.VS.mem v vs -> ssa_var_unchanged_program v p).
Proof.
  move=> H v Hmem.
  exact: (ssa_unchanged_program_mem H Hmem).
Qed.

Lemma ssa_unchanged_program_cons vs hd tl :
  ssa_vars_unchanged_program vs (hd::tl) ->
  ssa_vars_unchanged_instr vs hd /\ ssa_vars_unchanged_program vs tl.
Proof.
  move => H.
  move: (ssa_unchanged_program_local H) => {H} H.
  split.
  - apply: ssa_unchanged_instr_global => v Hmem.
    move: (H v Hmem) => {H} H.
    move: (ssa_var_unchanged_program_cons H) => [Hhd _].
    exact: Hhd.
  - apply: ssa_unchanged_program_global => v Hmem.
    move: (H v Hmem) => {H} H.
    move: (ssa_var_unchanged_program_cons H) => [_ Htl].
    exact: Htl.
Qed.

Lemma ssa_unchanged_program_hd vs hd tl :
  ssa_vars_unchanged_program vs (hd::tl) ->
  ssa_vars_unchanged_instr vs hd.
Proof.
  move=> Hun; move: (ssa_unchanged_program_cons Hun) => [Hhd Htl]; assumption.
Qed.

Lemma ssa_unchanged_program_tl vs hd tl :
  ssa_vars_unchanged_program vs (hd::tl) ->
  ssa_vars_unchanged_program vs tl.
Proof.
  move=> Hun; move: (ssa_unchanged_program_cons Hun) => [Hhd Htl]; assumption.
Qed.

Lemma ssa_unchanged_instr_singleton1 v i :
  ssa_vars_unchanged_instr (zSSA.VS.singleton v) i ->
  ssa_var_unchanged_instr v i.
Proof.
  move=> Hun.
  apply: (ssa_unchanged_instr_mem Hun).
  apply: zSSA.VSLemmas.mem_singleton2.
  exact: eqxx.
Qed.

Lemma ssa_unchanged_program_singleton1 v p :
  ssa_vars_unchanged_program (zSSA.VS.singleton v) p ->
  ssa_var_unchanged_program v p.
Proof.
  move=> Hun.
  apply: (ssa_unchanged_program_mem Hun).
  apply: zSSA.VSLemmas.mem_singleton2.
  exact: eqxx.
Qed.

Lemma ssa_unchanged_instr_singleton2 v i :
  ssa_var_unchanged_instr v i ->
  ssa_vars_unchanged_instr (zSSA.VS.singleton v) i.
Proof.
  move=> Hun.
  apply: ssa_unchanged_instr_global => x Hmem.
  move: (zSSA.VSLemmas.mem_singleton1 Hmem) => Heq.
  rewrite (eqP Heq); assumption.
Qed.

Lemma ssa_unchanged_program_singleton2 v p :
  ssa_var_unchanged_program v p ->
  ssa_vars_unchanged_program (zSSA.VS.singleton v) p.
Proof.
  move=> Hun.
  apply: ssa_unchanged_program_global => x Hmem.
  move: (zSSA.VSLemmas.mem_singleton1 Hmem) => Heq.
  rewrite (eqP Heq); assumption.
Qed.

Lemma ssa_unchanged_instr_union1 s1 s2 i :
  ssa_vars_unchanged_instr (zSSA.VS.union s1 s2) i ->
  ssa_vars_unchanged_instr s1 i /\ ssa_vars_unchanged_instr s2 i.
Proof.
  move=> Hun.
  move: (ssa_unchanged_instr_local Hun) => {Hun} Hun.
  split; apply: ssa_unchanged_instr_global => v Hmem.
  - apply: Hun.
    exact: zSSA.VSLemmas.mem_union2.
  - apply: Hun.
    exact: zSSA.VSLemmas.mem_union3.
Qed.

Lemma ssa_unchanged_program_union1 s1 s2 p :
  ssa_vars_unchanged_program (zSSA.VS.union s1 s2) p ->
  ssa_vars_unchanged_program s1 p /\ ssa_vars_unchanged_program s2 p.
Proof.
  move=> Hun.
  move: (ssa_unchanged_program_local Hun) => {Hun} Hun.
  split; apply: ssa_unchanged_program_global => v Hmem.
  - apply: Hun.
    exact: zSSA.VSLemmas.mem_union2.
  - apply: Hun.
    exact: zSSA.VSLemmas.mem_union3.
Qed.

Lemma ssa_unchanged_instr_union2 s1 s2 i :
  ssa_vars_unchanged_instr s1 i -> ssa_vars_unchanged_instr s2 i ->
  ssa_vars_unchanged_instr (zSSA.VS.union s1 s2) i.
Proof.
  move=> Hun1 Hun2.
  apply: ssa_unchanged_instr_global => x Hmem.
  move: (zSSA.VSLemmas.mem_union1 Hmem); case => {Hmem} Hmem.
  - exact: (ssa_unchanged_instr_mem Hun1 Hmem).
  - exact: (ssa_unchanged_instr_mem Hun2 Hmem).
Qed.

Lemma ssa_unchanged_program_union2 s1 s2 p :
  ssa_vars_unchanged_program s1 p -> ssa_vars_unchanged_program s2 p ->
  ssa_vars_unchanged_program (zSSA.VS.union s1 s2) p.
Proof.
  move=> Hun1 Hun2.
  apply: ssa_unchanged_program_global => x Hmem.
  move: (zSSA.VSLemmas.mem_union1 Hmem); case => {Hmem} Hmem.
  - exact: (ssa_unchanged_program_mem Hun1 Hmem).
  - exact: (ssa_unchanged_program_mem Hun2 Hmem).
Qed.

Lemma ssa_unchanged_instr_subset vs1 vs2 i :
  ssa_vars_unchanged_instr vs2 i ->
  zSSA.VS.subset vs1 vs2 ->
  ssa_vars_unchanged_instr vs1 i.
Proof.
  move=> Hun Hsub.
  move: (ssa_unchanged_instr_local Hun) => {Hun} Hun.
  apply: ssa_unchanged_instr_global.
  move=> v Hmem; apply: Hun.
  exact: (zSSA.VSLemmas.mem_subset Hmem Hsub).
Qed.

Lemma ssa_unchanged_program_subset vs1 vs2 p :
  ssa_vars_unchanged_program vs2 p ->
  zSSA.VS.subset vs1 vs2 ->
  ssa_vars_unchanged_program vs1 p.
Proof.
  move=> Hun Hsub.
  move: (ssa_unchanged_program_local Hun) => {Hun} Hun.
  apply: ssa_unchanged_program_global.
  move=> v Hmem; apply: Hun.
  exact: (zSSA.VSLemmas.mem_subset Hmem Hsub).
Qed.

Lemma ssa_unchanged_program_add1 v s p :
  ssa_vars_unchanged_program (zSSA.VS.add v s) p ->
  ssa_var_unchanged_program v p /\ ssa_vars_unchanged_program s p.
Proof.
  move=> H; split.
  - apply: (ssa_unchanged_program_mem H).
    exact: zSSA.VSLemmas.mem_add2.
  - apply: (ssa_unchanged_program_subset H).
    exact: (zSSA.VSLemmas.subset_add _ (zSSA.VSLemmas.subset_refl s)).
Qed.

Lemma ssa_unchanged_program_add2 v s p :
  ssa_var_unchanged_program v p /\ ssa_vars_unchanged_program s p ->
  ssa_vars_unchanged_program (zSSA.VS.add v s) p.
Proof.
  move=> [H1 H2].
  apply: ssa_unchanged_program_global => x Hmem.
  case: (zSSA.VSLemmas.mem_add1 Hmem) => {Hmem}.
  - move=> Heq.
    by rewrite (eqP Heq).
  - move=> Hmem.
    exact: (ssa_unchanged_program_mem H2 Hmem).
Qed.

Lemma ssa_unchanged_program_empty vs :
  ssa_vars_unchanged_program vs [::].
Proof.
  apply: ssa_unchanged_program_global => v Hv.
  done.
Qed.

Lemma ssa_unchanged_program_replace vs1 vs2 p :
  zSSA.VS.Equal vs1 vs2 ->
  ssa_vars_unchanged_program vs1 p ->
  ssa_vars_unchanged_program vs2 p.
Proof.
  move=> Heq H.
  move: (ssa_unchanged_program_local H) => {H} H.
  apply: ssa_unchanged_program_global => v Hv.
  apply: H.
  rewrite Heq.
  assumption.
Qed.

Lemma well_formed_ssa_vars_unchanged_hd vs hd tl :
  well_formed_ssa_program vs (hd::tl) ->
  ssa_vars_unchanged_program (zSSA.vars_instr hd) tl.
Proof.
  move => /andP [/andP [Hwf Huc] Hssa].
  apply: (@ssa_unchanged_program_replace
            (zSSA.VS.union (zSSA.lvs_instr hd) (zSSA.rvs_instr hd))).
  - rewrite -zSSA.vars_instr_split.
    reflexivity.
  - apply: ssa_unchanged_program_union2.
    + move/andP: Hssa => [Hssa1 Hssa2].
      exact: Hssa1.
    + apply: (@ssa_unchanged_program_subset _ vs).
      * exact: (ssa_unchanged_program_tl Huc).
      * apply: zSSA.well_formed_instr_subset_rvs.
        exact: (zSSA.well_formed_program_cons1 Hwf).
Qed.

Lemma well_formed_ssa_tl vs hd tl :
  well_formed_ssa_program vs (hd::tl) ->
  well_formed_ssa_program (zSSA.VS.union vs (zSSA.lvs_instr hd)) tl.
Proof.
  move=> Hwfssa.
  move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
  apply/andP; split; first (apply/andP; split).
  - exact: (zSSA.well_formed_program_cons2 Hwf).
  - apply: ssa_unchanged_program_union2.
    + exact: (ssa_unchanged_program_tl Huc).
    + move/andP: Hssa => [H _].
      exact: H.
  - move/andP: Hssa => [_ H].
    exact: H.
Qed.

Lemma ssa_unchanged_instr_eval_exp e s1 s2 i :
  ssa_vars_unchanged_instr (zSSA.vars_exp e) i ->
  zSSA.eval_instr s1 i = s2 ->
  zSSA.eval_exp e s1 = zSSA.eval_exp e s2.
Proof.
  elim: e => /=.
  - move=> v Hun Hi.
    move: (ssa_unchanged_instr_singleton1 Hun) => {Hun} Hun.
    exact: (acc_unchanged_instr Hun Hi).
  - reflexivity.
  - move=> op e IH Hun Hi.
    rewrite (IH Hun Hi); reflexivity.
  - move=> op e1 IH1 e2 IH2 Hun Hi.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hi) (IH2 Hun2 Hi); reflexivity.
  - move=> e IH p Hun Hi.
    rewrite (IH Hun Hi); reflexivity.
Qed.

Lemma ssa_unchanged_program_eval_exp e s1 s2 p :
  ssa_vars_unchanged_program (zSSA.vars_exp e) p ->
  zSSA.eval_program s1 p = s2 ->
  zSSA.eval_exp e s1 = zSSA.eval_exp e s2.
Proof.
  elim: e => /=.
  - move=> v /andP [Hunch _] Hp.
    exact: (acc_unchanged_program Hunch Hp).
  - move=> c _ Hp.
    reflexivity.
  - move=> op e IH Hunch Hp.
    rewrite (IH Hunch Hp).
    reflexivity.
  - move=> op e1 IH1 e2 IH2 Hunch Hp.
    move: (ssa_unchanged_program_union1 Hunch) => {Hunch} [Hunch1 Hunch2].
    rewrite (IH1 Hunch1 Hp) (IH2 Hunch2 Hp).
    reflexivity.
  - move=> e IH i Hunch Hp.
    rewrite (IH Hunch Hp).
    reflexivity.
Qed.

Lemma ssa_unchanged_instr_eval_bexp e s1 s2 i :
  ssa_vars_unchanged_instr (zSSA.vars_bexp e) i ->
  zSSA.eval_instr s1 i = s2 ->
  zSSA.eval_bexp e s1 <-> zSSA.eval_bexp e s2.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Hun Hi.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (ssa_unchanged_instr_eval_exp Hun1 Hi)
            (ssa_unchanged_instr_eval_exp Hun2 Hi).
    done.
  - move=> e1 e2 p Hun Hi.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (ssa_unchanged_instr_eval_exp Hun1 Hi)
            (ssa_unchanged_instr_eval_exp Hun2 Hi).
    done.
  - move=> e1 IH1 e2 IH2 Hun Hi.
    move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    rewrite (IH1 Hun1 Hi) (IH2 Hun2 Hi).
    done.
Qed.

Lemma ssa_unchanged_program_eval_bexp e s1 s2 p :
  ssa_vars_unchanged_program (zSSA.vars_bexp e) p ->
  zSSA.eval_program s1 p = s2 ->
  zSSA.eval_bexp e s1 <-> zSSA.eval_bexp e s2.
Proof.
  elim: e => /=.
  - done.
  - move=> e1 e2 Hunch Hp.
    move: (ssa_unchanged_program_union1 Hunch) => {Hunch} [Hunch1 Hunch2].
    rewrite (ssa_unchanged_program_eval_exp Hunch1 Hp)
            (ssa_unchanged_program_eval_exp Hunch2 Hp).
    done.
  - move=> e1 e2 i Hunch Hp.
    move: (ssa_unchanged_program_union1 Hunch) => {Hunch} [Hunch1 Hunch2].
    rewrite (ssa_unchanged_program_eval_exp Hunch1 Hp)
            (ssa_unchanged_program_eval_exp Hunch2 Hp).
    done.
  - move=> e1 IH1 e2 IH2 Hunch Hp.
    move: (ssa_unchanged_program_union1 Hunch) => {Hunch} [Hunch1 Hunch2].
    rewrite (IH1 Hunch1 Hp) (IH2 Hunch2 Hp).
    done.
Qed.

Lemma ssa_unchanged_program_eval_bexp1 e s1 s2 p :
  ssa_vars_unchanged_program (zSSA.vars_bexp e) p ->
  zSSA.eval_program s1 p = s2 ->
  zSSA.eval_bexp e s1 -> zSSA.eval_bexp e s2.
Proof.
  move=> Hunch Hp He.
  move: (ssa_unchanged_program_eval_bexp Hunch Hp) => [H1 H2].
  exact: (H1 He).
Qed.

Lemma ssa_unchanged_program_eval_bexp2 e s1 s2 p :
  ssa_vars_unchanged_program (zSSA.vars_bexp e) p ->
  zSSA.eval_program s1 p = s2 ->
  zSSA.eval_bexp e s2 -> zSSA.eval_bexp e s1.
Proof.
  move=> Hunch Hp He.
  move: (ssa_unchanged_program_eval_bexp Hunch Hp) => [H1 H2].
  exact: (H2 He).
Qed.

Lemma ssa_instr_le_unchanged m1 m2 i si :
  forall v iv,
    iv <=? get_index v m1 ->
    ssa_instr m1 i = (m2, si) ->
    ssa_var_unchanged_instr (v, iv) si.
Proof.
  elim: i m1 m2 si.
  - move=> x e m1 m2 si v iv Hiv Hsi.
    move: (ssa_zassign Hsi) => {Hsi} [Hupd Hsi].
    rewrite Hsi => {Hsi} /=.
    apply/negP => /= Hmem.
    move: (zSSA.VSLemmas.mem_singleton1 Hmem) => {Hmem} => Heq.
    move/eqP: Heq => [Hv Hi].
    rewrite Hv Hi Hupd in Hiv.
    exact: (get_upd_index_leF Hiv).
  - move=> vh vl e p m1 m2 si v iv Hiv Hsi.
    move: (ssa_zsplit Hsi) => {Hsi} [Hupd Hsi].
    rewrite Hsi => {Hsi} /=.
    apply/negP => /= Hmem.
    move: (zSSA.VSLemmas.mem_add1 Hmem); case => {Hmem} Hmem.
    + move/eqP: Hmem => [Hv Hi].
      rewrite Hv Hi in Hiv => {Hv Hi v iv}.
      exact: (get_upd_index_leF Hiv).
    + move: (zSSA.VSLemmas.mem_singleton1 Hmem) => {Hmem} Heq.
      move/eqP: Heq => [Hv Hi].
      rewrite Hv Hi in Hiv => {Hv Hi v iv}.
      move: (get_upd_index_le m1 vl vh) => Hle.
      move: (get_upd_index_lt (upd_index vh m1) vl) => Hlt.
      move: (Nleq_ltn_trans Hle Hlt) => {Hle Hlt} Hlt.
      move: (Nleq_ltn_trans Hiv Hlt) => {Hiv Hlt} Hlt.
      rewrite -Hupd Nltnn in Hlt.
      done.
Qed.

Lemma ssa_program_le_unchanged m1 m2 p sp :
  forall v i,
    i <=? get_index v m1 ->
    ssa_program m1 p = (m2, sp) ->
    ssa_var_unchanged_program (v, i) sp.
Proof.
  elim: p m1 m2 sp.
  - move=> m1 m2 sp v i Hi /= [Hm Hp].
    by rewrite -Hp.
  - move=> hd tl IH m1 m2 sp v i Hle Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    rewrite Hsp => {Hsp sp} /=.
    apply/andP; split.
    + exact: (ssa_instr_le_unchanged Hle Hshd).
    + move: (ssa_instr_index_le v Hshd) => Hle2.
      move: (Nleq_trans Hle Hle2) => {Hle Hle2} Hle.
      exact: (IH _ _ _ _ _ Hle Hstl).
Qed.

Theorem ssa_program_single_assignment m1 m2 p sp :
  ssa_program m1 p = (m2, sp) ->
  ssa_single_assignment sp.
Proof.
  elim: p m1 m2 sp.
  - move=> m1 m2 sp Hsp.
    rewrite ssa_program_empty in Hsp.
    case: Hsp => Hm Hsp.
    rewrite -Hsp; done.
  - move=> hd tl IH m1 m2 sp Hsp.
    move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
    rewrite Hsp => {Hsp sp}.
    apply/andP; split.
    + case: hd Hshd.
      * move=> v e Hshd /=.
        move: (ssa_zassign Hshd) => {Hshd} [Hupd Hshd].
        rewrite Hshd /= => {Hshd shd}.
        apply: ssa_unchanged_program_singleton2.
        apply: (ssa_program_le_unchanged _ Hstl).
        exact: Nleqnn.
      * move=> vh vl e p Hshd.
        move: (ssa_zsplit Hshd) => {Hshd} [Hupd Hshd].
        rewrite Hshd /= => {Hshd shd}.
        apply: ssa_unchanged_program_add2; split;
          [idtac | apply ssa_unchanged_program_singleton2].
        -- apply: (ssa_program_le_unchanged _ Hstl).
           rewrite Hupd.
           exact: get_upd_index_le.
        -- apply: (ssa_program_le_unchanged _ Hstl).
           exact: Nleqnn.
    + exact: (IH _ _ _ Hstl).
Qed.

Lemma ssa_instr_well_formed vs m1 m2 i si :
  well_formed_instr vs i ->
  ssa_instr m1 i = (m2, si) ->
  zSSA.well_formed_instr (ssa_vars m1 vs) si.
Proof.
  elim: i vs m1 m2 si => /=.
  - move=> v e vs m1 m2 si Hsub [Hupd Hsi].
    rewrite -Hsi /= ssa_vars_exp_subset.
    assumption.
  - move=> vh vl e p vs m1 m2 si /andP [Hhl Hsub] [Hupd Hsi].
    rewrite -Hsi /= ssa_vars_exp_subset.
    apply/andP; split; last by assumption.
    exact: (pair_neq1 _ _ Hhl).
Qed.

Definition dclosed m ivs lvs svs : Prop :=
  (* Indices of unused variables should not be updated. *)
  (forall v, ~~ VS.mem v (VS.union ivs lvs) -> get_index v m = 0) /\
  (* The index of a variable in lvs should start from 1. *)
  (forall v, VS.mem v lvs -> 0 <? get_index v m) /\
  (* svs contains all versions of ivs and lvs. *)
  (forall v i, zSSA.VS.mem (v, i) svs = (VS.mem v ivs) && (i <=? get_index v m) || (VS.mem v lvs) && (0 <? i <=? get_index v m)).

Lemma dclosed_not_mem m ivs lvs svs v :
  dclosed m ivs lvs svs ->
  ~~ VS.mem v (VS.union ivs lvs) ->
  get_index v m = 0.
Proof.
  move=> [Hd _] Hmem.
  exact: (Hd v Hmem).
Qed.

Lemma dclosed_mem1 m ivs lvs svs v i :
  dclosed m ivs lvs svs ->
  zSSA.VS.mem (v, i) svs ->
  (VS.mem v ivs) /\ (i <=? get_index v m) \/
                    (VS.mem v lvs) /\ (0 <? i <=? get_index v m).
Proof.
  move=> [_ [_ Hd]] Hmem.
  rewrite Hd in Hmem.
  case: (orP Hmem) => {Hmem} /andP H.
  - left; assumption.
  - right; assumption.
Qed.

Lemma dclosed_mem2 m ivs lvs svs v i :
  dclosed m ivs lvs svs ->
  VS.mem v ivs -> i <=? get_index v m ->
  zSSA.VS.mem (v, i) svs.
Proof.
  move=> [_ [_ Hd]] Hmem Hi.
  rewrite Hd.
  apply/orP; left; apply/andP; split; assumption.
Qed.

Lemma dclosed_mem3 m ivs lvs svs v i :
  dclosed m ivs lvs svs ->
  VS.mem v lvs -> 0 <? i <=? get_index v m ->
  zSSA.VS.mem (v, i) svs.
Proof.
  move=> [_ [_ Hd]] Hmem Hi.
  rewrite Hd.
  apply/orP; right; apply/andP; split; assumption.
Qed.

Lemma dclosed_mem4 m ivs lvs svs v :
  dclosed m ivs lvs svs ->
  VS.mem v lvs -> 0 <? get_index v m.
Proof.
  move=> [_ [Hd _]] Hmem.
  exact: (Hd _ Hmem).
Qed.

Lemma dclosed_mem5 m ivs lvs svs v i :
  dclosed m ivs lvs svs ->
  0 <? i <=? get_index v m ->
  zSSA.VS.mem (v, i) svs.
Proof.
  move=> Hd Hi.
  case Hmem: (VS.mem v (VS.union ivs lvs)).
  - case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
    + move/andP: Hi => [Hi1 Hi2].
      exact: (dclosed_mem2 Hd Hmem Hi2).
    + exact: (dclosed_mem3 Hd Hmem Hi).
  - move/idP/negP: Hmem => Hmem.
    rewrite (dclosed_not_mem Hd Hmem) in Hi.
    move/andP: Hi => [Hi1 Hi2].
    rewrite Nleqn0 in Hi2.
    rewrite (eqP Hi2) Nltnn in Hi1.
    discriminate.
Qed.

Lemma dclosed_empty vs :
  dclosed empty_vmap vs VS.empty (ssa_vars empty_vmap vs).
Proof.
  split; first by reflexivity.
  split; first by discriminate.
  move=> v i.
  case Hmem: (VS.mem v vs && (i <=? get_index v empty_vmap)
              || [&& VS.mem v VS.empty, 0 <? i & i <=? get_index v empty_vmap]).
  - case: (orP Hmem) => {Hmem} /andP [Hmem Hidx].
    + apply: (ssa_vars_mem3 Hmem).
      rewrite get_index_empty Nleqn0 in Hidx *.
      exact: (eqP Hidx).
    + discriminate.
  - apply/negP => H.
    move/negP: Hmem; apply.
    move: (ssa_vars_mem2 H) => [y [[Hy Hidy] Hmemy]].
    apply/orP; left; apply/andP; split.
    + rewrite Hy; exact: Hmemy.
    + rewrite Hidy Hy; exact: Nleqnn.
Qed.

Lemma dclosed_subset m ivs lvs svs :
  dclosed m ivs lvs svs ->
  zSSA.VS.subset (ssa_vars m (VS.union ivs lvs)) svs.
Proof.
  move=> [Hd1 [Hd2 Hd3]].
  apply: zSSA.VS.subset_1 => x /zSSA.VSLemmas.memP Hmem.
  apply/zSSA.VSLemmas.memP.
  move: Hmem; rewrite ssa_vars_union => Hmem.
  destruct x as [x i].
  rewrite Hd3; apply/orP.
  case: (zSSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
  - left.
    move: (ssa_vars_mem2 Hmem) => [y [[Hxy Hidx] Hmemy]].
    apply/andP; split.
    + rewrite Hxy; exact: Hmemy.
    + rewrite Hidx Hxy; exact: Nleqnn.
  - right.
    move: (ssa_vars_mem2 Hmem) => [y [[Hxy Hidx] Hmemy]].
    apply/andP; split.
    + rewrite Hxy; exact: Hmemy.
    + move: (Hd2 _ Hmemy) => H.
      rewrite Hxy Hidx; apply/andP; split.
      * assumption.
      * exact: Nleqnn.
Qed.

Lemma dclosed_instr_well_formed ivs lvs svs m1 m2 i si :
  well_formed_instr (VS.union ivs lvs) i ->
  ssa_instr m1 i = (m2, si) ->
  dclosed m1 ivs lvs svs ->
  zSSA.well_formed_instr svs si.
Proof.
  elim: i ivs lvs m1 m2 si => /=.
  - move=> v e ivs lvs m1 m2 si Hsub [Hupd Hsi] Hd.
    rewrite -Hsi /=.
    apply: (zSSA.VSLemmas.subset_trans (s2:=ssa_vars m1 (VS.union ivs lvs))).
    + rewrite ssa_vars_exp_subset.
      assumption.
    + exact: dclosed_subset.
  - move=> vh vl e p ivs lvs m1 m2 si /andP [Hhl Hsub] [Hupd Hsi] Hd.
    rewrite -Hsi /=.
    apply/andP; split; first by exact: (pair_neq1 _ _ Hhl).
    apply: (zSSA.VSLemmas.subset_trans (s2:=ssa_vars m1 (VS.union ivs lvs))).
    + rewrite ssa_vars_exp_subset.
      assumption.
    + exact: dclosed_subset.
Qed.

Lemma dclosed_upd1 m ivs lvs svs v x i :
  dclosed m ivs lvs svs ->
  VS.mem x ivs ->
  i <=? get_index x (upd_index v m) ->
  zSSA.VS.mem (x, i) (zSSA.VS.add (ssa_var (upd_index v m) v) svs).
Proof.
  move=> Hd Hmem Hi.
  case Hxv: (x == v).
  - rewrite (eqP Hxv) in Hmem Hi *.
    rewrite Nleq_eqVlt in Hi.
    case: (orP Hi) => {Hi} Hi.
    + rewrite /ssa_var -(eqP Hi).
      exact: zSSA.VSLemmas.mem_add2.
    + rewrite get_upd_index_eq NltnS in Hi.
      apply: zSSA.VSLemmas.mem_add3.
      exact: (dclosed_mem2 Hd Hmem Hi).
  - move/idP/negP: Hxv => Hxv.
    rewrite (get_upd_index_neq _ Hxv) in Hi.
    apply: zSSA.VSLemmas.mem_add3.
    exact: (dclosed_mem2 Hd Hmem Hi).
Qed.

Lemma dclosed_upd2 m ivs lvs svs v x i :
  dclosed m ivs lvs svs ->
  0 <? i <=? get_index x (upd_index v m) ->
  zSSA.VS.mem (x, i) (zSSA.VS.add (ssa_var (upd_index v m) v) svs).
Proof.
  move=> Hd /andP [Hi1 Hi2].
  case Hxv: (x == v).
  - rewrite (eqP Hxv) in Hi2 * => {x Hxv}.
    rewrite Nleq_eqVlt in Hi2.
    case: (orP Hi2) => {Hi2} Hi2.
    + apply: zSSA.VSLemmas.mem_add2.
      rewrite /ssa_var -(eqP Hi2).
      exact: eqxx.
    + rewrite get_upd_index_eq NltnS in Hi2.
      apply: zSSA.VSLemmas.mem_add3.
      have: 0 <? i <=? get_index v m by rewrite Hi1 Hi2.
      move=> Hi.
      exact: (dclosed_mem5 Hd Hi).
  - move/idP/negP: Hxv => Hxv.
    rewrite (get_upd_index_neq _ Hxv) in Hi2.
    have: 0 <? i <=? get_index x m by rewrite Hi1 Hi2.
    move=> Hi.
    apply: zSSA.VSLemmas.mem_add3.
    exact: (dclosed_mem5 Hd Hi).
Qed.

Lemma dclosed_upd3 m ivs lvs svs vh vl x i :
  dclosed m ivs lvs svs ->
  VS.mem x ivs ->
  i <=? get_index x (upd_index vl (upd_index vh m)) ->
  zSSA.VS.mem (x, i)
             (zSSA.VS.add (ssa_var (upd_index vh m) vh)
                         (zSSA.VS.add (ssa_var (upd_index vl (upd_index vh m)) vl) svs)).
Proof.
  move=> Hd Hmem Hi.
  case Hxl: (x == vl).
  - rewrite (eqP Hxl) in Hi Hmem * => {x Hxl}.
    rewrite Nleq_eqVlt in Hi.
    case: (orP Hi) => {Hi} Hi.
    + apply: zSSA.VSLemmas.mem_add3.
      apply: zSSA.VSLemmas.mem_add2.
      rewrite /ssa_var -(eqP Hi).
      exact: eqxx.
    + rewrite get_upd_index_eq NltnS in Hi.
      rewrite zSSA.VSLemmas.OP.P.add_union_singleton.
      rewrite zSSA.VSLemmas.OP.P.add_union_singleton.
      rewrite (zSSA.VSLemmas.OP.P.union_sym _ svs).
      rewrite -zSSA.VSLemmas.OP.P.union_assoc.
      apply: zSSA.VSLemmas.mem_union2.
      rewrite -zSSA.VSLemmas.OP.P.add_union_singleton.
      exact: (dclosed_upd1 Hd Hmem Hi).
  - move/idP/negP: Hxl => Hxl.
    rewrite (get_upd_index_neq _ Hxl) in Hi.
    rewrite zSSA.VSLemmas.OP.P.add_union_singleton.
    rewrite zSSA.VSLemmas.OP.P.add_union_singleton.
    rewrite (zSSA.VSLemmas.OP.P.union_sym _ svs).
    rewrite -zSSA.VSLemmas.OP.P.union_assoc.
    apply: zSSA.VSLemmas.mem_union2.
    rewrite -zSSA.VSLemmas.OP.P.add_union_singleton.
    exact: (dclosed_upd1 Hd Hmem Hi).
Qed.

Lemma dclosed_upd4 m ivs lvs svs vh vl x i :
  dclosed m ivs lvs svs ->
  0 <? i <=? get_index x (upd_index vl (upd_index vh m)) ->
  zSSA.VS.mem (x, i)
             (zSSA.VS.add (ssa_var (upd_index vh m) vh)
                         (zSSA.VS.add (ssa_var (upd_index vl (upd_index vh m)) vl) svs)).
Proof.
  move=> Hd /andP [Hi1 Hi2].
  case Hxl: (x == vl).
  - rewrite (eqP Hxl) in Hi2 * => {x Hxl}.
    rewrite Nleq_eqVlt in Hi2.
    case: (orP Hi2) => {Hi2} Hi2.
    + apply: zSSA.VSLemmas.mem_add3.
      apply: zSSA.VSLemmas.mem_add2.
      rewrite /ssa_var -(eqP Hi2).
      exact: eqxx.
    + rewrite get_upd_index_eq NltnS in Hi2.
      have: 0 <? i <=? get_index vl (upd_index vh m) by rewrite Hi1 Hi2.
      move=> Hi.
      rewrite zSSA.VSLemmas.OP.P.add_union_singleton.
      rewrite zSSA.VSLemmas.OP.P.add_union_singleton.
      rewrite (zSSA.VSLemmas.OP.P.union_sym _ svs).
      rewrite -zSSA.VSLemmas.OP.P.union_assoc.
      apply: zSSA.VSLemmas.mem_union2.
      rewrite -zSSA.VSLemmas.OP.P.add_union_singleton.
      exact: (dclosed_upd2 Hd Hi).
  - move/idP/negP: Hxl => Hxl.
    rewrite (get_upd_index_neq _ Hxl) in Hi2.
    have: 0 <? i <=? get_index x (upd_index vh m) by rewrite Hi1 Hi2.
    move=> Hi.
    rewrite zSSA.VSLemmas.OP.P.add_union_singleton.
    rewrite zSSA.VSLemmas.OP.P.add_union_singleton.
    rewrite (zSSA.VSLemmas.OP.P.union_sym _ svs).
    rewrite -zSSA.VSLemmas.OP.P.union_assoc.
    apply: zSSA.VSLemmas.mem_union2.
    rewrite -zSSA.VSLemmas.OP.P.add_union_singleton.
    exact: (dclosed_upd2 Hd Hi).
Qed.

Lemma dclosed_zassign_succ :
  forall (v : var) (e : exp) (ivs lvs : VS.t) (svs : zSSA.VS.t)
         (m1 m2 : vmap) (si : zSSA.instr),
    dclosed m1 ivs lvs svs ->
    (upd_index v m1, ssa_var (upd_index v m1) v @:= ssa_exp m1 e) = (m2, si) ->
    dclosed m2 ivs (VS.union lvs (VS.singleton v))
            (zSSA.VS.union svs (zSSA.lvs_instr si)).
Proof.
  move=> v e ivs lvs svs m1 m2 si Hd [Hm Hsi].
  rewrite -Hsi /= => {Hsi}.
  split; [idtac | split].
  - move=> x.
    rewrite -VSLemmas.OP.P.union_assoc.
    move=> Hmem.
    move: (VSLemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
    move: (VSLemmas.not_mem_singleton1 Hmem2) => /negP Hne.
    move: (dclosed_not_mem Hd Hmem1) => Hidx.
    rewrite -Hm (get_upd_index_neq _ Hne).
    exact: Hidx.
  - move=> x Hmem.
    case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
    + move: (dclosed_mem4 Hd Hmem) => Hlt.
      rewrite -Hm.
      exact: (Nltn_leq_trans Hlt (get_upd_index_le m1 x v)).
    + move: (VSLemmas.mem_singleton1 Hmem) => /eqP Hxv.
      rewrite Hxv -Hm.
      exact: get_upd_index_gt0.
  - move=> x i.
    case H: (VS.mem x ivs && (i <=? get_index x m2) || [&& VS.mem x (VS.union lvs (VS.singleton v)), 0 <? i & i <=? get_index x m2]).
    + case: (orP H) => {H} /andP [Hmem Hi].
      * rewrite zSSA.VSLemmas.OP.P.union_sym -zSSA.VSLemmas.OP.P.add_union_singleton.
        rewrite -Hm in Hi.
        exact: (dclosed_upd1 Hd Hmem Hi).
      * rewrite zSSA.VSLemmas.OP.P.union_sym -zSSA.VSLemmas.OP.P.add_union_singleton.
        rewrite -Hm in Hi.
        exact: (dclosed_upd2 Hd Hi).
    + apply/negP => Hmemx.
      move/negP: H; apply.
      apply/orP.
      case: (zSSA.VSLemmas.mem_union1 Hmemx) => {Hmemx} Hmemx.
      * move: (dclosed_mem1 Hd Hmemx); case; move => [Hx Hi].
        -- left; apply/andP; split; first by exact: Hx.
           rewrite -Hm.
           exact: (Nleq_trans Hi (get_upd_index_le m1 x v)).
        -- right; apply/andP; split;
           first by apply: VSLemmas.mem_union2; exact: Hx.
           move/andP: Hi => [Hi1 Hi2].
           apply/andP; split; first by exact: Hi1.
           rewrite -Hm.
           exact: (Nleq_trans Hi2 (get_upd_index_le m1 x v)).
      * move: (zSSA.VSLemmas.mem_singleton1 Hmemx) => {Hmemx} /eqP [Hx Hi].
        right; apply/andP; split.
        -- rewrite Hx; apply: VSLemmas.mem_union3;
           exact: VSLemmas.mem_singleton2.
        -- rewrite Hx -Hm; apply/andP; split; last by rewrite Hi; exact: Nleqnn.
           rewrite Hi.
           exact: (get_upd_index_gt0).
Qed.

Lemma dclosed_zsplit_succ :
  forall (v v0 : var) (e : exp) (p : positive) (ivs lvs : VS.t)
         (svs : zSSA.VS.t) (m1 m2 : vmap) (si : zSSA.instr),
    dclosed m1 ivs lvs svs ->
    (upd_index v0 (upd_index v m1),
     zSSA.zSplit (ssa_var (upd_index v m1) v)
                (ssa_var (upd_index v0 (upd_index v m1)) v0)
                (ssa_exp m1 e) p) = (m2, si) ->
    dclosed m2 ivs (VS.union lvs (VS.add v (VS.singleton v0)))
            (zSSA.VS.union svs (zSSA.lvs_instr si)).
Proof.
  move=> vh vl e p ivs lvs svs m1 m2 si Hd [Hm Hsi].
  rewrite -Hsi /= => {Hsi}.
  split; [idtac | split].
  - move=> v.
    rewrite -VSLemmas.OP.P.union_assoc.
    move=> Hmem.
    move: (VSLemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
    move: (VSLemmas.not_mem_add1 Hmem2) => {Hmem2} [/negP Hneh Hmem3].
    move: (VSLemmas.not_mem_singleton1 Hmem3) => {Hmem3} /negP Hnel.
    move: (dclosed_not_mem Hd Hmem1) => Hi.
    rewrite -Hm (get_upd_index_neq _ Hnel) (get_upd_index_neq _ Hneh).
    exact: Hi.
  - move=> v Hmem.
    rewrite -Hm => {Hm}.
    case: (VSLemmas.mem_union1 Hmem) => {Hmem} Hmem;
      [idtac | case: (VSLemmas.mem_add1 Hmem) => {Hmem} Hmem].
    + move: (dclosed_mem4 Hd Hmem) => Hlt.
      move: (get_upd_index_le m1 v vh) => Hle.
      move: (Nltn_leq_trans Hlt Hle) => {Hlt Hle} Hlt.
      move: (get_upd_index_le (upd_index vh m1) v vl) => Hle.
      exact: (Nltn_leq_trans Hlt Hle).
    + rewrite (eqP Hmem).
      move: (get_upd_index_le (upd_index vh m1) vh vl) => Hle.
      move: (get_upd_index_gt0 m1 vh) => Hlt.
      exact: (Nltn_leq_trans Hlt Hle).
    + move: (VSLemmas.mem_singleton1 Hmem) => {Hmem} Heq.
      rewrite (eqP Heq).
      exact: (get_upd_index_gt0 _ vl).
  - move=> v i.
    rewrite zSSA.VSLemmas.OP.P.add_union_singleton.
    rewrite (zSSA.VSLemmas.OP.P.union_sym (zSSA.VS.singleton _)).
    rewrite -zSSA.VSLemmas.OP.P.union_assoc.
    rewrite (zSSA.VSLemmas.OP.P.union_sym svs).
    rewrite (zSSA.VSLemmas.OP.P.union_sym _ (zSSA.VS.singleton _)).
    rewrite -zSSA.VSLemmas.OP.P.add_union_singleton.
    rewrite -zSSA.VSLemmas.OP.P.add_union_singleton.
    case H:  (VS.mem v ivs && (i <=? get_index v m2) || [&& VS.mem v (VS.union lvs (VS.add vh (VS.singleton vl))), 0 <? i & i <=? get_index v m2]).
    + rewrite -Hm in H.
      case: (orP H) => {H} /andP [Hmem Hi].
      * exact: (dclosed_upd3 Hd Hmem Hi).
      * exact: (dclosed_upd4 Hd Hi).
    + apply/negP => Hmem.
      move/negP: H; apply.
      apply/orP.
      case: (zSSA.VSLemmas.mem_add1 Hmem) => {Hmem} Hmem; [
          idtac |
          case: (zSSA.VSLemmas.mem_add1 Hmem) => {Hmem} Hmem
        ].
      * move/eqP: Hmem => [Hv Hi].
        right; apply/andP; split.
        -- apply: VSLemmas.mem_union3.
           apply: VSLemmas.mem_add2.
           rewrite Hv; exact: eqxx.
        -- rewrite get_upd_index_eq in Hi.
           rewrite -Hm Hv Hi => {i Hi}.
           apply/andP; split.
           ++ exact: Nltn0Sn.
           ++ rewrite -NltnS.
              rewrite Nltn_add2r.
              move: (get_upd_index_lt m1 vh) => Hlt.
              move: (get_upd_index_le (upd_index vh m1) vh vl) => Hle.
              exact: (Nltn_leq_trans Hlt Hle).
      * move/eqP: Hmem => [Hv Hi].
        right; apply/andP; split.
        -- apply: VSLemmas.mem_union3.
           apply: VSLemmas.mem_add3.
           apply: VSLemmas.mem_singleton2.
           rewrite Hv; exact: eqxx.
        -- rewrite get_upd_index_eq in Hi.
           rewrite -Hm Hv Hi => {i Hi v Hv Hm}.
           set m3 := upd_index vh m1.
           apply/andP; split.
           ++ exact: Nltn0Sn.
           ++ rewrite -NltnS.
              rewrite Nltn_add2r.
              exact: (get_upd_index_lt m3 vl) => Hlt.
      * move: (get_upd_index_le m1 v vh) => Hle1.
        move: (get_upd_index_le (upd_index vh m1) v vl) => Hle2.
        move: (Nleq_trans Hle1 Hle2) => {Hle1 Hle2} Hle.
        case: (dclosed_mem1 Hd Hmem); move=> [Hv Hi].
        -- left; apply/andP; split; first by assumption.
           rewrite -Hm.
           exact: (Nleq_trans Hi Hle).
        -- right; apply/andP; split; first by apply: VSLemmas.mem_union2.
           move/andP: Hi => [Hi1 Hi2].
           apply/andP; split; first by assumption.
           rewrite -Hm.
           exact: (Nleq_trans Hi2 Hle).
Qed.

Corollary dclosed_instr_succ ivs lvs svs m1 m2 i si :
  dclosed m1 ivs lvs svs ->
  ssa_instr m1 i = (m2, si) ->
  dclosed m2 ivs (VS.union lvs (lvs_instr i)) (zSSA.VS.union svs (zSSA.lvs_instr si)).
Proof.
  elim: i ivs lvs svs m1 m2 si => /=.
  - exact: dclosed_zassign_succ.
  - exact: dclosed_zsplit_succ.
Qed.

Theorem dclosed_program_well_formed ivs lvs svs m1 m2 p sp :
  well_formed_program (VS.union ivs lvs) p ->
  ssa_program m1 p = (m2, sp) ->
  dclosed m1 ivs lvs svs ->
  well_formed_ssa_program svs sp.
Proof.
  move=> Hwell Hssa Hd.
  apply/andP; split; [apply/andP; split | idtac].
  - elim: p ivs lvs svs m1 m2 sp Hwell Hssa Hd => /=.
    + move=> ivs lvs svs m1 m2 sp _ [Hm Hsp] Hd.
      rewrite -Hsp.
      done.
    + move=> hd tl IH ivs lvs svs m1 m2 sp /andP [Hhd Htl] Hsp Hd.
      move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
      rewrite Hsp => {Hsp sp}.
      apply/andP; split.
      * exact: (dclosed_instr_well_formed Hhd Hshd).
      * apply: (IH ivs (VS.union lvs (lvs_instr hd)) _ _ _ _ _ Hstl);
          last by exact: (dclosed_instr_succ Hd Hshd).
        apply: (well_formed_program_replace Htl).
        rewrite VSLemmas.OP.P.union_assoc.
        rewrite (VSLemmas.OP.P.union_sym lvs (lvs_instr hd)).
        reflexivity.
  - apply: ssa_unchanged_program_global => v Hmem.
    destruct v as [v i].
    apply: (ssa_program_le_unchanged _ Hssa).
    case: (dclosed_mem1 Hd Hmem) => {Hmem}; case => Hmem Hi.
    + exact: Hi.
    + move/andP: Hi => [Hi1 Hi2].
      exact: Hi2.
  - exact: (ssa_program_single_assignment Hssa).
Qed.

Corollary ssa_program_well_formed vs m p sp :
  well_formed_program vs p ->
  ssa_program empty_vmap p = (m, sp) ->
  well_formed_ssa_program (ssa_vars empty_vmap vs) sp.
Proof.
  move=> Hwell Hsp.
  have: well_formed_program (VS.union vs VS.empty) p
    by apply: (well_formed_program_replace Hwell);
    rewrite (VSLemmas.OP.P.empty_union_2 vs VS.empty_1);
    reflexivity.
  move=> {Hwell} Hwell.
  apply: (dclosed_program_well_formed Hwell Hsp).
  exact: dclosed_empty.
Qed.

Lemma ssa_exp_var_index m e v i :
  zSSA.VS.mem (v, i) (zSSA.vars_exp (ssa_exp m e)) ->
  get_index v m = i.
Proof.
  elim: e m v i.
  - move=> v m x i Hmem.
    move/zSSA.VSLemmas.memP: Hmem => Hin.
    move: (zSSA.VS.singleton_1 Hin) => /eqP [] Hv Hi.
    rewrite -Hv; exact: Hi.
  - move=> c m x i Hmem.
    discriminate.
  - move=> op e IH m x i Hmem.
    exact: (IH _ _ _ Hmem).
  - move=> op e1 IH1 e2 IH2 m x i Hmem.
    move/zSSA.VSLemmas.memP: Hmem => Hin.
    move: {Hin} (zSSA.VS.union_1 Hin); case => /zSSA.VSLemmas.memP Hmem.
    + apply: (IH1 _ _ _ Hmem); reflexivity.
    + apply: (IH2 _ _ _ Hmem); reflexivity.
  - move=> e IH p n v i /= Hmem.
    exact: (IH _ _ _ Hmem).
Qed.

Lemma ssa_bexp_var_index m e v i :
  zSSA.VS.mem (v, i) (zSSA.vars_bexp (ssa_bexp m e)) ->
  get_index v m = i.
Proof.
  elim: e m v i => /=.
  - move=> m v i Hmem.
    discriminate.
  - move=> e1 e2 m v i Hmem.
    rewrite zSSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem;
    apply: (ssa_exp_var_index Hmem); reflexivity.
  - move=> e1 e2 p m v i Hmem.
    rewrite zSSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem;
    apply: (ssa_exp_var_index Hmem); reflexivity.
  - move=> e1 IH1 e2 IH2 m v i Hmem.
    rewrite zSSA.VSLemmas.union_b in Hmem.
    move/orP: Hmem; case=> Hmem.
    + apply: (IH1 _ _ _ Hmem); reflexivity.
    + apply: (IH2 _ _ _ Hmem); reflexivity.
Qed.

Lemma ssa_spec_in_pre_unchanged s v :
  zSSA.VS.mem v (zSSA.vars_bexp (zSSA.spre (ssa_spec s))) ->
  ssa_var_unchanged_program v (zSSA.sprog (ssa_spec s)).
Proof.
  move: (ssa_spec_unfold s) => [m [Hpre [Hprog Hpost]]].
  move=> Hmem.
  rewrite Hpre in Hmem.
  destruct v as [v i].
  move: (ssa_bexp_var_index Hmem) => Hidx.
  apply: (ssa_program_le_unchanged (m1:=empty_vmap)).
  - rewrite Hidx.
    exact: Nleqnn.
  - symmetry; exact: Hprog.
Qed.

Lemma ssa_spec_unchanged_pre s :
  ssa_vars_unchanged_program (zSSA.vars_bexp (zSSA.spre (ssa_spec s))) (zSSA.sprog (ssa_spec s)).
Proof.
  move: (ssa_spec_unfold s) => [m [Hpre [Hprog Hpost]]].
  destruct s as [f p g]; rewrite /= in Hpre Hprog Hpost *.
  apply: ssa_unchanged_program_global => v Hmem.
  exact: ssa_spec_in_pre_unchanged.
Qed.

Theorem ssa_spec_well_formed vs s :
  well_formed_spec vs s ->
  well_formed_ssa_spec (ssa_vars empty_vmap vs) (ssa_spec s).
Proof.
  move=> /andP [/andP [Hsubpre Hwellprog] Hsubpost].
  move: (ssa_spec_unfold s) => [m [Hpre [Hprog Hpost]]].
  move: (ssa_program_well_formed Hwellprog (Logic.eq_sym Hprog)) => /andP [/andP [Hwell Hvs] Hsingle].
  apply/andP; split; [apply/andP; split | idtac].
  - apply/andP; split; [apply/andP; split | idtac].
    + rewrite Hpre ssa_vars_bexp_subset.
      assumption.
    + assumption.
    + rewrite Hpost.
      exact: (ssa_vars_post_subset Hsubpost (Logic.eq_sym Hprog)).
  - assumption.
  - exact: (ssa_program_single_assignment (Logic.eq_sym Hprog)).
Qed.

Close Scope N_scope.