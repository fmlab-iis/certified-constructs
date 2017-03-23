From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype.
From Common Require Import Types Lists FSets Bools ZAriths Var Store.
From mQhasm Require Import zDSL zSSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* Convert SSA programs to Boolean expressions *)

Section SSAPoly.

  Import zSSA.

  Local Open Scope zssa_scope.

  Definition bexp_instr (i : instr) : bexp :=
    match i with
    | zAssign v e => zVar v @= e
    | zSplit vh vl e p => (zVar vl) @+ (zVar vh @* (zConst 2 @^ p)) @= e
    end.

  Definition bexp_program (p : program) : seq bexp :=
    map bexp_instr p.

  Record bexp_spec : Type :=
    mkPolySpec { bpre : bexp;
                 bprog : seq bexp;
                 bpost : bexp }.

  Definition bexp_of_spec (s : spec) : bexp_spec :=
    {| bpre := spre s;
       bprog := bexp_program (sprog s);
       bpost := spost s |}.

  Lemma bexp_instr_vars i :
    VS.Equal (vars_bexp (bexp_instr i)) (vars_instr i).
  Proof.
    elim: i => /=.
    - move=> v e.
      rewrite -VSLemmas.OP.P.add_union_singleton.
      reflexivity.
    - move=> vh vl e _.
      rewrite (VSLemmas.OP.P.empty_union_2 (VS.singleton vh) VS.empty_1).
      rewrite (VSLemmas.OP.P.union_sym (VS.singleton vl) _).
      rewrite VSLemmas.OP.P.union_assoc.
      rewrite -VSLemmas.OP.P.add_union_singleton.
      rewrite -VSLemmas.OP.P.add_union_singleton.
      reflexivity.
  Qed.

  Lemma bexp_instr_ssa_vars_unchanged i p :
    ssa_vars_unchanged_program (vars_instr i) p ->
    ssa_vars_unchanged_program (vars_bexp (bexp_instr i)) p.
  Proof.
    move => H.
    apply: (ssa_unchanged_program_replace _ H) => {H}.
    rewrite bexp_instr_vars.
    reflexivity.
  Qed.

  Lemma bexp_instr_eval vs i s1 s2 :
    well_formed_instr vs i ->
    ssa_vars_unchanged_instr vs i ->
    eval_instr s1 i = s2 ->
    eval_bexp (bexp_instr i) s2.
  Proof.
    elim: i.
    - move=> v e Hsub Hun Hi /=.
      rewrite /= in Hsub.
      move: (ssa_unchanged_instr_subset Hun Hsub) => {Hun} Hun.
      rewrite -(ssa_unchanged_instr_eval_exp Hun Hi) -Hi (State.acc_upd_eq _ _ (eqxx v)).
      reflexivity.
    - move=> vh vl e p /andP [Hhl Hsub] Hun Hi /=.
      move: (ssa_unchanged_instr_subset Hun Hsub) => {Hun} Hun.
      rewrite -(ssa_unchanged_instr_eval_exp Hun Hi) -Hi /= => {Hi Hsub Hun}.
      set ev := eval_exp e s1.
      set x := Z.div_eucl ev (Z.pow_pos 2 p).
      have: x = Z.div_eucl ev (Z.pow_pos 2 p) by reflexivity.
      destruct x as [q r].
      move=> Hqr.
      rewrite (State.acc_upd2_eq1 _ _ _ (eqxx vh) Hhl)
              (State.acc_upd2_eq2 _ _ _ _ (eqxx vl)).
      have: (Z.pow_pos 2 p > 0)%Z by apply: Zpow_pos_gt0.
      move=> H2p.
      move: (Z_div_mod ev (Z.pow_pos 2 p) H2p).
      rewrite -Hqr.
      move=> [Hev _].
      rewrite Zplus_comm Zmult_comm -Hev.
      reflexivity.
  Qed.



  Fixpoint eval_bexps_conj (es : seq bexp) (s : State.t) : Prop :=
    match es with
    | [::] => True
    | hd::tl => eval_bexp hd s /\ eval_bexps_conj tl s
    end.

  Lemma bexp_program_eval vs p s1 s2 :
    well_formed_ssa_program vs p ->
    eval_program s1 p = s2 ->
    eval_bexps_conj (bexp_program p) s2.
  Proof.
    elim: p vs s1 s2 => /=.
    - done.
    - move=> hd tl IH vs s1 s2 Hwfssa Hep.
      move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
      split.
      + apply: (ssa_unchanged_program_eval_bexp1 _ Hep).
        * exact: (bexp_instr_ssa_vars_unchanged
                    (well_formed_ssa_vars_unchanged_hd Hwfssa)).
        * apply: (bexp_instr_eval
                    (well_formed_program_cons1 Hwf)
                    (ssa_unchanged_program_hd Huc)).
          reflexivity.
      + exact: (IH _ _ _ (well_formed_ssa_tl Hwfssa) Hep).
  Qed.

  Definition valid_bexp_spec_conj (s : bexp_spec) : Prop :=
    forall st : State.t,
      eval_bexp (bpre s) st ->
      eval_bexps_conj (bprog s) st ->
      eval_bexp (bpost s) st.

  Lemma bexp_spec_sound_conj (vs : VS.t) (s : spec) :
    well_formed_ssa_spec vs s ->
    valid_bexp_spec_conj (bexp_of_spec s) -> valid_spec s.
  Proof.
    destruct s as [f p g].
    rewrite /bexp_of_spec /valid_bexp_spec_conj /=.
    move=> Hwfssa Hvalid s1 s2 /= Hf Hp.
    apply: Hvalid.
    - move: Hwfssa => /andP /= [/andP [Hwf Huc] Hssa].
      apply: (ssa_unchanged_program_eval_bexp1 _ Hp Hf).
      apply: (ssa_unchanged_program_subset Huc).
      move/andP: Hwf => /= [/andP [H _] _].
      exact: H.
    - exact: (bexp_program_eval (well_formed_ssa_spec_program Hwfssa) Hp).
  Qed.



  Fixpoint eval_bexps_imp (es : seq bexp) (s : State.t) (p : Prop) : Prop :=
    match es with
    | [::] => p
    | hd::tl => eval_bexp hd s -> eval_bexps_imp tl s p
    end.

  Definition valid_bexp_spec_imp (s : bexp_spec) : Prop :=
    forall st : State.t,
      eval_bexp (bpre s) st ->
      eval_bexps_imp (bprog s) st (eval_bexp (bpost s) st).

  Lemma valid_bexp_spec_conj_imp (s : bexp_spec) :
    valid_bexp_spec_conj s -> valid_bexp_spec_imp s.
  Proof.
    destruct s as [f p g].
    move => Hc s /= Hf.
    move: (Hc s Hf) => /= {Hc Hf f} Hc.
    elim: p Hc => /=.
    - by apply.
    - move=> hd tl IH Hc Hhd.
      apply: IH => Htl.
      apply: Hc; split; assumption.
  Qed.

  Lemma valid_bexp_spec_imp_conj (s : bexp_spec) :
    valid_bexp_spec_imp s -> valid_bexp_spec_conj s.
  Proof.
    destruct s as [f p g].
    move => Hi s /= Hf.
    move: (Hi s Hf) => /= {Hi Hf f} Hi.
    elim: p Hi => /=.
    - done.
    - move=> hd tl IH Hi [Hhd Htl].
      exact: (IH (Hi Hhd) Htl).
  Qed.

  Lemma bexp_spec_sound_imp (vs : VS.t) (s : spec) :
    well_formed_ssa_spec vs s ->
    valid_bexp_spec_imp (bexp_of_spec s) -> valid_spec s.
  Proof.
    move=> Hw Hv.
    apply: (bexp_spec_sound_conj Hw).
    exact: valid_bexp_spec_imp_conj.
  Qed.



  Definition valid_bexp_spec := valid_bexp_spec_imp.

  Theorem bexp_spec_sound (vs : VS.t) (s : spec) :
    well_formed_ssa_spec vs s ->
    valid_bexp_spec (bexp_of_spec s) -> valid_spec s.
  Proof.
    exact: bexp_spec_sound_imp.
  Qed.

  Local Close Scope zssa_scope.

End SSAPoly.
