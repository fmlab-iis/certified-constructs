
From Coq Require Import List.
From Coq Require Import ZArith.
From PolyOp Require Import PolyOp.

Open Scope Z_scope.



(********************************************)
(* Test for positive constant in Z          *)
(********************************************)

Ltac NCst t :=
  match t with
  | O => constr:(1%positive)
  | Zpos ?t1 => t1
  | _ => constr:false
  end.

(********************************************)
(* Belonging in a list for Z                *)
(********************************************)

Ltac rIN a l :=
  match l with
  | (cons a ?l) => constr:true
  | (cons _ ?l) => rIN a l
  | _ => constr:false
  end.

(********************************************)
(* Adding a variable in a list for Z        *)
(********************************************)

Ltac rAddFv a l :=
  match (rIN a l) with
  | true => l
  | _ => constr:(cons a l)
  end.

(********************************************)
(* Adding a variable in a list for Z        *)
(********************************************)

Ltac rFind_at a l :=
  match l with
  | (cons a _) => constr:xH
  | (cons _ ?l) =>
    let p := rFind_at a l in
    let v := constr:(Psucc p) in
    let v1 := eval compute in v in
    v1
  | _ => constr:xH
 end.

(********************************************)
(* Computing the list of variables for Z    *)
(********************************************)

Ltac variables t :=
  let rec aux t fv :=
  match t with
  | 0 => fv
  | 1 => fv
  | Zpos _ => fv
  | Zneg _ => fv
  | False  => fv
  | ?t1 -> ?g1 =>
    let fv1  := aux t1 fv in
    let fv2  := aux g1 fv1 in fv2
  | (_ <= ?t1) => aux t1 fv
  | (_ < ?t1) => aux t1 fv
  | (?t1 = _) => aux t1 fv
  | (?t1 + ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in fv2
  | (?t1 * ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in fv2
  | (?t1 - ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in fv2
  | (-?t1) =>
    let fv1  := aux t1 fv in fv1
  | (?t1 ^ ?t2) =>
    let fv1  := aux t1 fv in
    match NCst t2 with
    | false => let fv1 := rAddFv t fv in fv1
    | _ => fv1
    end
  | _ => let fv1 := rAddFv t fv in fv1
  end in
  aux t (@nil Z).

(********************************************)
(* Syntaxification tactic for Z             *)
(********************************************)

Ltac abstrait t fv :=
  let rec aux t :=
  match t with
  | 0 => uconstr:(Const 0 1)
  | 1 => uconstr:(Const 1 1)
  | 2 => uconstr:(Const 2 1)
  | Zpos _ => uconstr:(Const t 1)
  | Zneg _ => uconstr:(Const t 1)
  | (?t1 + ?t2) =>
    let v1  := aux t1 in
    let v2  := aux t2 in uconstr:(Add v1 v2)
  | (?t1 * ?t2) =>
    let v1  := aux t1 in
    let v2  := aux t2 in uconstr:(Mul v1 v2)
  | (?t1 - ?t2) =>
    let v1  := aux t1 in
    let v2  := aux t2 in uconstr:(Sub v1 v2)
  | (?t1 ^ 0) =>
    uconstr:(Const 1 1)
  | (?t1 ^ ?n) =>
    match NCst n with
    | false => let p := rFind_at t fv in uconstr:(Var p)
    | ?n1 => let v1  := aux t1 in uconstr:(Pow v1 n1)
    end
  | (- ?t1) =>
    let v1  := aux t1 in uconstr:(Opp v1)
  | _ =>
    let p := rFind_at t fv in uconstr:(Var p)
  end in
  aux t.

(********************************************)
(* Unsyntaxification for Z                  *)
(********************************************)

Fixpoint interpret t fv {struct t} : Z :=
  match t with
  | (Add t1 t2) =>
    let v1  := interpret t1 fv in
    let v2  := interpret t2 fv in (v1 + v2)
  | (Mul t1 t2) =>
    let v1  := interpret t1 fv in
    let v2  := interpret t2 fv in (v1 * v2)
  | (Sub t1 t2) =>
    let v1  := interpret t1 fv in
    let v2  := interpret t2 fv in (v1 - v2)
  | (Opp t1) =>
    let v1  := interpret t1 fv in (-v1)
  | (Pow t1 t2) =>
    let v1  := interpret t1 fv in v1 ^ (Zpos t2)
  | (Const t1 t2) =>  t1
  | (Var n) => nth (pred (nat_of_P n)) fv 0
  | Zero => 0
  end.

Ltac simplZ :=
  cbv beta iota zeta delta -[Zmult Zplus Zpower Z.pow_pos Zminus Zopp Zdiv Zmod].

Ltac modp_find_witness_with eng :=
  match goal with
  | |- exists k : Z, ?p = k * ?c =>
    let l := variables p in
    let ap := abstrait p l in
    let ac := abstrait c l in
    pdiv_with eng ap ac ltac:(fun w =>
      let w := constr:(interpret w l) in
      idtac "Witness:" w;
      time "validate witness" (exists w; simplZ; ring)
    )
  end.

Tactic Notation "modp_find_witness" := (modp_find_witness_with default_engine).

Close Scope Z_scope.
