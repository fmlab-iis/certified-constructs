
From Coq Require Import ZArith.

Inductive engine : Set :=
| Singular
| Magma.

Definition default_engine : engine := Singular.

Inductive term : Set :=
| Zero : term
| Const : Z -> positive -> term
| Var : positive -> term
| Opp : term -> term
| Add : term -> term -> term
| Sub : term -> term -> term
| Mul : term -> term -> term
| Pow : term -> positive -> term.

Declare ML Module "polyop_plugin".

Ltac pdiv_with eng p c k :=
  let id := fresh in
  pdiv_ml eng id p c;
  let res := eval compute in id in
  k res.

Ltac pdiv p c k := pdiv_with Singular p c k || pdiv_with Magma p c k.