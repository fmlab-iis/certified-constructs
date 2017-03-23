
From mathcomp Require Import ssreflect ssrbool.

(** General tactics *)

Ltac splitP := apply/andP; split.

Ltac leftP := apply/orP; left.

Ltac rightP := apply/orP; right.

Ltac caseP H :=
  match type of H with
  | is_true ([&& _, _ & _ ]) =>
    let H0 := fresh in
    let H1 := fresh in
    move/andP: H => [H0 H1]; caseP H1; first [caseP H0 | move: H0]
  | is_true ([&& _ & _ ]) =>
    let H0 := fresh in
    let H1 := fresh in
    move/andP: H => [H0 H1]; first [caseP H1 | move: H1]; first [caseP H0 | move: H0]
  | is_true (_ && _) =>
    let H0 := fresh in
    let H1 := fresh in
    move/andP: H => [H0 H1]; first [caseP H1 | move: H1]; first [caseP H0 | move: H0]
  | [/\ _, _, _, _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseP H1 | move: H1]; first [caseP H0 | move: H0]
  | [/\ _, _, _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseP H1 | move: H1]; first [caseP H0 | move: H0]
  | [/\ _, _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseP H1 | move: H1]; first [caseP H0 | move: H0]
  | [/\ _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseP H1 | move: H1]; first [caseP H0 | move: H0]
  | _ /\ _ =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseP H1 | move: H1]; first [caseP H0 | move: H0]
  | is_true ([|| _, _ | _ ]) =>
    let H0 := fresh in
    move/orP: H; case; [idtac | move=> H0; caseP H0]
  | is_true ([|| _ | _ ]) => move/orP: H; case
  | is_true (_ || _) => move/orP: H; case
  | [\/ _, _, _ | _ ] => elim: H
  | [\/ _, _ | _ ] => elim: H
  | [\/ _ | _ ] => elim: H
  | _ \/ _ => elim: H
  end.

Ltac applyP H :=
  match goal with
  | H: is_true (negb _) |- False => apply: (negP H) => H
  | H: is_true (negb _) |- is_true (negb _) =>
    let H0 := fresh in
    apply/negP => H0; apply: (negP H); move: H0
  end.

