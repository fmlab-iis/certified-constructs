From Coq Require Export ZArith.
Open Scope Z_scope.

Definition modulo (a b p : Z) := exists k : Z, a - b = k * p.

Ltac simplZ2 :=
   cbv beta iota zeta delta -[Zmult Zplus Zpower Z.pow_pos Zminus Zopp Zdiv Zmod].

Lemma gbsimplZ1 : forall x : Z, x ^ 1 = x.
Proof.
  exact Z.pow_1_r.
Qed.

Lemma gbsimplZ2 : forall x : Z, 0 * x = 0.
Proof.
  exact Z.mul_0_l.
Qed.

Lemma gbsimplZ3 : forall x : Z, x * 0 = 0.
Proof.
  exact Z.mul_0_r.
Qed.

Lemma gbsimplZ4 : forall x : Z, 1 * x = x.
Proof.
  exact Z.mul_1_l.
Qed.

Lemma gbsimplZ5 : forall x : Z, 0 + x = x.
Proof.
  exact Z.add_0_l.
Qed.

Lemma gbsimplZ6 : forall x : Z, x * 1 = x.
Proof.
  exact Z.mul_1_r.
Qed.

Lemma gbsimplZ7 : forall x : Z, (-1) * x = - x.
Proof.
  intros; ring.
Qed.

Lemma gbsimplZ8 n p :
  Z.pow_pos n p = n ^ (Zpos p).
Proof.
  exact (Z.pow_pos_fold n p).
Qed.

Lemma gbsimplZ9 n p :
  Zpower_nat n p = n ^ (Z.of_nat p).
Proof.
  rewrite Zpower_nat_Z.
  reflexivity.
Qed.

Ltac simplZ3 :=
  repeat (rewrite gbsimplZ1 || rewrite gbsimplZ2 || rewrite gbsimplZ3
          || rewrite gbsimplZ4 || rewrite gbsimplZ5 || rewrite gbsimplZ6
          || rewrite gbsimplZ7 || rewrite gbsimplZ8 || rewrite gbsimplZ9).

Ltac simplZ := simplZ2; simplZ3.

Ltac remove_exists_hyp :=
  match goal with
  | H : exists x : Z, _ |- _ =>
    let x := fresh "x" in
    elim H; clear H; intros x H
  end.

Ltac gbarith_choice o := fail 100 "This evaluation version does not contain gbarith developed by Loic Pottier.".
