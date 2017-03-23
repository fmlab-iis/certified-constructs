
From Coq Require Import OrderedType ZArith String.
From mathcomp Require Import ssreflect ssrbool ssrnat ssralg ssrfun.
From mathcomp Require Import eqtype div zmodp.
From mathcomp Require Export tuple.
From Bits Require Export bits.
From Common Require Import Nats ZAriths Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Close Scope bits_scope.

Notation "x + y" := (addB x y) : bits_scope.
Notation "x - y" := (subB x y) : bits_scope.
Notation "x * y" := (mulB x y) : bits_scope.
Notation "x < y" := (ltB x y) : bits_scope.
Notation "x <= y" := (leB x y) : bits_scope.



(** Constants *)

Inductive nstring (n : nat) : Set :=
| NString : forall s : string, String.length s = n -> nstring n.

Notation "n .-string" := (nstring n) (at level 4, format "n .-string") : type_scope.

Definition fromNString (n : nat) (s : n.-string) : BITS (n * 4).
Proof.
  destruct s as [s Hlen].
  rewrite -Hlen.
  exact: (fromHex s).
Defined.



(** Lemmas *)

Section BitsLemmas.

  Set Implicit Arguments.

  Lemma ltBnn : forall (n : nat) (x : BITS n), ltB x x = false.
  Proof.
    move=> n x.
    rewrite ltB_nat.
    apply: ltnn.
  Qed.

  Ltac have_incB_m n :=
    let m := fresh n "_dec" in
    let H := fresh in
    set m := decB n;
    have H : n = incB m; [by rewrite (decBK n) | ].

  Ltac have_incB_b n :=
    let m := fresh n "_dec" in
    let H := fresh in
    set m := decB n;
    have H : n == incB m; [by rewrite (decBK n) | ].

  Ltac have_decB_m n :=
    let m := fresh n "_inc" in
    let H := fresh in
    set m := incB n;
    have H : n = decB m; [by rewrite (incBK n) | ].

  Ltac have_decB_b n :=
    let m := fresh n "_inc" in
    let H := fresh in
    set m := incB n;
    have H : n == decB m; [by rewrite (incBK n) | ].

  Inductive bounded_nat (n : nat) : nat -> Set :=
  | BoundedNat : forall m : nat, (m < n) -> bounded_nat n m.

  Lemma bits_bounded : forall (n : nat) (x : BITS n), bounded_nat (2^n) (toNat x).
  Proof.
    move=> n x.
    apply: BoundedNat.
    exact: (toNatBounded x).
  Qed.

  Lemma bits_rect :
    forall (n : nat) (P : BITS n -> Type),
      P (zero n) ->
      (forall x : BITS n, P x -> P (incB x)) ->
      forall x : BITS n, P x.
  Proof.
    move=> n P Hbase Hind x.
    move: (bits_bounded x) => Hbounded.
    rewrite -(toNatK x).
    induction Hbounded.
    elim: m i.
    - move=> Hlt.
      rewrite fromNat0.
      exact: Hbase.
    - move=> m IHm Hlt.
      rewrite -incB_fromNat.
      apply: Hind.
      apply: IHm.
      exact: (ltnW Hlt).
  Qed.

  Lemma bits_ind :
    forall (n : nat) (P : BITS n -> Prop),
      P (zero n) ->
      (forall x : BITS n, P x -> P (incB x)) ->
      forall x : BITS n, P x.
  Proof.
    exact: bits_rect.
  Qed.

  Lemma bits_rec :
    forall (n : nat) (P : BITS n -> Set),
      P (zero n) ->
      (forall x : BITS n, P x -> P (incB x)) ->
      forall x : BITS n, P x.
  Proof.
    exact: bits_rect.
  Qed.

  Lemma behead_tuple_zero : forall n : nat, behead_tuple (zero n.+1) == zero n.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma behead_tuple_fromNat0 : forall n : nat, behead_tuple (n:=n.+1) #0 == #0.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma thead_zero : forall n : nat, thead (zero n.+1) == false.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma thead_fromNat0 : forall n : nat, thead (n:=n.+1) #0 == false.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma behead_tuple_ones : forall n : nat, behead_tuple (ones n.+1) == ones n.
  Proof.
    move=>n.
    apply: eqxx.
  Qed.

  Lemma thead_ones : forall n : nat, thead (ones n.+1) == true.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma bits_ne0_toNat_gt0 :
    forall (n : nat) (x : BITS n), (x != #0) == (0 < toNat x).
  Proof.
    move=> n x.
    rewrite -{1}(toNatK x).
    set m := toNat x.
    have nat_eq0_gt0: forall n : nat, (n == 0) || (n > 0) by move=> i; elim: i.
    case: (orP (nat_eq0_gt0 m)) => {nat_eq0_gt0} Hm.
    - rewrite (eqP Hm) => {x m Hm}.
      rewrite ltnn.
      apply/eqP/negPf/negPf.
      exact: eqxx.
    - rewrite Hm.
      apply/eqP/negP.
      rewrite -fromNatBounded_eq.
      + move=> Heq.
        rewrite (eqP Heq) in Hm.
        done.
      + exact: toNatBounded.
      + rewrite expn_gt0.
        apply/orP; by left.
  Qed.

  Lemma toPosZ_nil (x : BITS 0) : toPosZ x = 0%Z.
  Proof.
    by rewrite (tuple0 x).
  Qed.

  Lemma toPosZ_zero n : toPosZ (zero n) = 0%Z.
  Proof.
    rewrite /toPosZ.
    elim: n => /=.
    - reflexivity.
    - move=> n Hind.
      rewrite Hind Z.double_spec.
      reflexivity.
  Qed.

  Lemma toPosZ_min n (x : BITS n) : Z.le 0 (toPosZ x).
  Proof.
    destruct x as [x Hsize].
    rewrite /toPosZ => {Hsize n} /=.
    elim: x => /=.
    - done.
    - move=> b x.
      set n := (seq.foldr
                  (fun (b : bool) (z : Z) =>
                     if b then Z.succ (Z.double z) else Z.double z) (0%Z) x).
      move=> Hind /=.
      move: (Zdouble_positive Hind) => H.
      case Hb: b.
      + apply: (Zle_trans _ _ _ Hind).
        apply: (Zle_trans _ _ _ H).
        exact: Zle_succ.
      + exact: (Zle_trans _ _ _ Hind H).
  Qed.

  Lemma toPosZ_max n : forall (x : BITS n), Z.lt (toPosZ x) (two_power_nat n).
  Proof.
    elim: n.
    - move=> x.
      rewrite toPosZ_nil.
      exact: zero_lt_two_power_nat.
    - move=> n IHn.
      case/tupleP => [b x].
      case Hb: b; rewrite /toPosZ /=; fold (toPosZ x).
      + rewrite /Z.succ Z.double_spec two_power_nat_S.
        apply: ltn_Sdouble.
        exact: IHn.
      + rewrite Z.double_spec two_power_nat_S.
        apply: (Zmult_gt_0_lt_compat_l _ _ _ _ (IHn x)).
        done.
  Qed.

End BitsLemmas.



(** Ordering *)

Module BitsOrder <: OrderedType.

  Variable n : nat.

  Definition t := BITS n.

  Definition eq : t -> t -> Prop := fun x y : t => x == y.

  Definition lt : t -> t -> Prop := fun x y : t => ltB x y.

  Hint Unfold eq lt.

  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    exact: eq_refl.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    move=> x y.
    by rewrite /eq eq_sym.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    move=> x y z.
    rewrite /eq => Hxy Hyz.
    move/eqP: Hxy => Hxy.
    move/eqP: Hyz => Hyz.
    apply/eqP.
    by rewrite Hxy Hyz.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> x y z.
    exact: ltB_trans.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    move=> x y Hlt.
    move/eqP => Heq.
    apply/idP: Hlt.
    by rewrite Heq ltBnn.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    apply: bits_rec.
    - move=> y.
      case Hy0: (y == #0).
      + move/eqP: Hy0 => Hy0; rewrite Hy0.
        rewrite fromNat0.
        apply: EQ.
        exact: eq_refl.
      + apply: LT.
        rewrite /lt ltB_nat.
        rewrite toNat_zero.
        rewrite -(eqP (bits_ne0_toNat_gt0 y)).
        apply/negP.
        by rewrite Hy0.
    - move=> x Hind y.
      move: (toNat_incB x).
      case Hx: (x == ones n) => /= Hincx.
      + move: (toNat_decB y).
        case Hy: (y == #0) => /= Hdecy.
        * apply: EQ.
          rewrite /eq (eqP Hx) (eqP Hy) incB_ones fromNat0.
          exact: eqxx.
        * apply: LT.
          rewrite /lt ltB_nat Hincx.
          rewrite -(eqP (bits_ne0_toNat_gt0 y)).
          apply/negPf.
          exact: Hy.
      + move: (toNat_decB y).
        case Hy: (y == #0) => /= Hdecy.
        * apply: GT.
          rewrite /lt ltB_nat Hincx (eqP Hy) toNat_fromNat0.
          done.
        * move: (Hind (decB y)) => {Hind} Hind.
          case: Hind => Hcomp.
          -- apply: LT.
             rewrite /lt (ltB_nat x (decB y)) Hdecy in Hcomp.
             rewrite /lt (ltB_nat (incB x) y) Hincx.
             by rewrite -(eqP (lt_sub1r_add1l (toNat x) (toNat y))).
          -- apply: EQ.
             rewrite /eq in Hcomp *.
             rewrite (eqP Hcomp).
             by rewrite (decBK y).
          -- apply: GT.
             rewrite /lt ltB_nat Hdecy in Hcomp.
             rewrite /lt ltB_nat Hincx.
             rewrite -(ltn_add2r 1 ((toNat y).-1) (toNat x)) in Hcomp.
             have: (0 < toNat y).
             ++ rewrite -(eqP (bits_ne0_toNat_gt0 y)).
                apply/negP.
                by rewrite Hy.
             ++ move=> H0y.
                rewrite addn1 addn1 in Hcomp.
                rewrite (prednK H0y) in Hcomp.
                done.
  Qed.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    move=> x y.
    apply: eq_comparable.
  Qed.

End BitsOrder.



(** Overflows *)

Section BitsOverflow.

  (* Test if x + y will overflow. *)
  Definition addB_ovf (n : nat) (x y : BITS n) : bool :=
    match adcB false x y with
    | (false, _) => false
    | (true, _) => true
    end.

  Lemma toNat_addB_bounded :
    forall (n : nat) (x y : BITS n),
      ~~ addB_ovf x y ->
      toNat (addB x y) == (toNat x + toNat y).
  Proof.
    move=> n x y.
    rewrite /addB_ovf /adcB.
    rewrite -(toNat_adcBmain false x y).
    rewrite -{3}(splitmsbK (adcBmain false x y)).
    case: (splitmsb (adcBmain false x y)).
    move=> carry p.
    case: carry => //=.
    move=> _.
    rewrite toNat_joinmsb.
    exact: eqxx.
  Qed.

  Lemma leB_addB_ovf :
    forall (n : nat) (x y a b : BITS n),
      (a <= x)%bits -> (b <= y)%bits -> ~~ addB_ovf x y -> ~~ addB_ovf a b.
  Proof.
  Abort.

  (* Test if x - y will overflow. *)
  Definition subB_ovf (n : nat) (x y : BITS n) : bool :=
    match sbbB false x y with
    | (false, _) => false
    | (true, _) => true
    end.

  Lemma subB_ovf_ltB :
    forall (n : nat) (x y : BITS n), ~~ subB_ovf x y -> (y <= x)%bits.
  Proof.
    move=> n x y.
    rewrite /subB_ovf.
    move: (sbbB_ltB_leB x y).
    case: (sbbB false x y).
    move=> carry p.
    by case: carry.
  Qed.

  Lemma toNat_subB_bounded :
    forall (n : nat) (x y : BITS n),
      ~~ subB_ovf x y ->
      toNat (subB x y) == (toNat x - toNat y).
  Proof.
    move=> n x y H.
    apply/eqP.
    apply: toNat_subB.
    by apply: subB_ovf_ltB.
  Qed.

  (* Test if x * y will overflow. *)
  Definition mulB_ovf (n : nat) (x y : BITS n) : bool :=
    high n (fullmulB x y) != #0.

  Definition toNat_mulB_bounded :
    forall (n : nat) (x y : BITS n),
      ~~ mulB_ovf x y ->
      toNat (mulB x y) == (toNat x) * (toNat y).
  Proof.
    move=> n x y.
    rewrite /mulB_ovf /mulB => Hh.
    move: (toNat_fullmulB x y).
    move/negPn/eqP: Hh.
    rewrite toNat_low.
    rewrite {2 3}(split2eta (fullmulB x y)).
    set h := high n (fullmulB x y).
    set l := low n (fullmulB x y).
    rewrite toNatCat => Hh.
    rewrite Hh toNat_fromNat0 mul0n add0n.
    move=> Hxy; rewrite -Hxy.
    move: (toNatBounded l) => Hbounded.
    rewrite (modn_small Hbounded).
    exact: eqxx.
  Qed.

End BitsOverflow.



(** Intervals *)

Section BitsInterval.

  Local Open Scope bits_scope.

  Definition min (n : nat) (x y : BITS n) :=
    if x < y then x else y.

  Definition max (n : nat) (x y : BITS n) :=
    if x < y then y else x.

  Inductive intv_op : Set :=
  | LT
  | LE.

  Definition eval_intv_op (op : intv_op) (n : nat) : BITS n -> BITS n -> bool :=
    match op with
    | LT => ltB (n := n)
    | LE => leB (n := n)
    end.

  Definition interval (n : nat) (a : BITS n) (op1 : intv_op) (x : BITS n) (op2 : intv_op) (b : BITS n) : bool :=
    eval_intv_op op1 a x && eval_intv_op op2 x b.

  Notation "x ∈ [ a , b ]" := (interval a LE x LE b) (at level 20) : bits_scope.
  Notation "x ∈ ( a , b ]" := (interval a LT x LE b) (at level 20) : bits_scope.
  Notation "x ∈ [ a , b )" := (interval a LE x LT b) (at level 20) : bits_scope.
  Notation "x ∈ ( a , b )" := (interval a LT x LT b) (at level 20) : bits_scope.

  Ltac case_intv H :=
    move: H; rewrite /interval /eval_intv_op => H; caseP H.

  Definition intv_op_join (op1 op2 : intv_op) :=
    match op1, op2 with
    | LE, LE => LE
    | LT, LE
    | LE, LT
    | LT, LT => LT
    end.

  Lemma intv_addB (n : nat) (a : BITS n) op1 x op2 b c op3 y op4 d :
    interval a op1 x op2 b -> interval c op3 y op4 d ->
    ~~ addB_ovf a b -> ~~ addB_ovf b d ->
    interval (a + c) (intv_op_join op1 op3) (x + y) (intv_op_join op2 op4) (b + d).
  Proof.
  Abort.

End BitsInterval.
